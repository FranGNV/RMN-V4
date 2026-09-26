#!/usr/bin/env python3
"""Renomme des archives ZIP ou des dossiers Bruker : NOM_SOLVANT_NOYAU.

Sans argument, ouvre une interface graphique. Avec des arguments, traite une
archive, un dossier de ZIP ou, avec --dossier-bruker, un dossier de données
Bruker non compressées. Les originaux restent intacts.
"""
from __future__ import annotations

import argparse
import copy
import os
import queue
import re
import shutil
import sys
import tempfile
import threading
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


@dataclass(frozen=True)
class BrukerName:
    title: str
    solvent: str
    nucleus: str

    @property
    def filename(self) -> str:
        return "_".join((safe(self.title, 120), safe(self.solvent, 32),
                         safe(self.nucleus, 24))) + ".zip"


@dataclass
class Job:
    source: Path
    destination: Path
    renamed_members: dict[str, str] | None = None
    notes: tuple[str, ...] = ()
    kind: str = "single"


@dataclass
class FolderJob:
    source: Path
    destination: Path
    directories: list[tuple[Path, Path]]
    files: list[tuple[Path, Path]]
    renamed: int
    notes: tuple[str, ...]
    total_bytes: int


def decode_title(raw: bytes) -> str:
    for encoding in ("utf-8-sig", "cp1252", "latin-1"):
        try:
            text = raw.decode(encoding)
            break
        except UnicodeDecodeError:
            continue
    # Chez Bruker, SEULE la première ligne est le nom saisi par l'utilisateur.
    # La deuxième peut contenir la méthode, le chemin, le compte et le solvant.
    lines = text.replace("\x00", "").splitlines()
    return lines[0].strip() if lines else ""


def safe(value: str, limit: int) -> str:
    value = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", value)
    value = re.sub(r"\s+", " ", value).strip(" ._")[:limit].rstrip(" ._")
    if not value:
        raise ValueError("Champ de nom vide dans les données Bruker")
    if value.upper().split(".")[0] in {
        "CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)),
        *(f"LPT{i}" for i in range(1, 10)),
    }:
        value = "_" + value
    return value


def acquisition(raw: bytes) -> tuple[str, str]:
    text = raw.decode("latin-1", errors="replace")

    def parameter(key: str) -> str:
        match = re.search(r"^##\$" + key + r"=\s*(?:<([^>]*)>|([^\r\n]*))",
                          text, re.M | re.I)
        if not match:
            return ""
        return (match.group(1) if match.group(1) is not None
                else match.group(2)).strip()

    solvent = parameter("SOLVENT")
    isotope = parameter("NUC1")
    nucleus = re.fullmatch(r"\d*([A-Za-z]+)", isotope)
    if not solvent or not nucleus:
        raise ValueError("SOLVENT ou NUC1 absent de acqus")
    return solvent, nucleus.group(1).capitalize()


def records_in_bruker_zip(archive: zipfile.ZipFile) -> dict[str, BrukerName]:
    names = set(archive.namelist())
    found: dict[str, BrukerName] = {}
    for title_path in sorted(names):
        if not re.search(r"(?:^|/)pdata/\d+/title$", title_path, re.I):
            continue
        title = decode_title(archive.read(title_path))
        acq_path = title_path.rsplit("/pdata/", 1)[0] + "/acqus"
        if acq_path not in names:
            raise ValueError(f"acqus manquant près de {title_path}")
        if not title:
            # Garder une identification traçable lorsque le titre est vide.
            experiment = title_path.rsplit("/pdata/", 1)[0]
            parts = experiment.split("/")
            title = parts[-2] if len(parts) >= 2 else parts[-1]
        solvent, nucleus = acquisition(archive.read(acq_path))
        found[title_path] = BrukerName(title, solvent, nucleus)
    return found


def names_in_bruker_zip(archive: zipfile.ZipFile) -> set[BrukerName]:
    return set(records_in_bruker_zip(archive).values())


def raw_folder_mapping(archive: zipfile.ZipFile,
                       records: dict[str, BrukerName]) -> dict[str, str]:
    """Renommer les dossiers des jeux Bruker et leurs PDF exportés.

    Le contenu de chaque fichier reste intact. Les noms techniques fid, acqus,
    title, etc. restent utilisables par Bruker. Une expérience multi-noyaux
    dans un seul dossier sera signalée sans produire de sortie partielle.
    """
    groups: dict[tuple[str, ...], set[BrukerName]] = {}
    for title_path, meta in records.items():
        match = re.match(r"^(.*)/\d+/pdata/\d+/title$", title_path, re.I)
        if not match:
            raise ValueError("Structure de dossier Bruker non reconnue : " + title_path)
        root = tuple(part for part in match.group(1).split("/") if part)
        groups.setdefault(root, set()).add(meta)
    if any(len(values) != 1 for values in groups.values()):
        raise ValueError("Plusieurs analyses dans un même dossier Bruker ; "
                         "renommage du dossier ambigu.")
    roots = sorted(groups)
    if len(roots) < 2:
        raise ValueError("Plusieurs analyses dans un seul dossier Bruker ; "
                         "nom d'archive unique impossible.")
    common = 0
    while (all(len(root) > common for root in roots) and
           len({root[common].casefold() for root in roots}) == 1):
        common += 1
    if any(len(root) <= common for root in roots):
        raise ValueError("Dossiers Bruker imbriqués : renommage ambigu.")
    branches: dict[str, BrukerName] = {}
    for root in roots:
        branch = "/".join(root[:common + 1])
        meta = next(iter(groups[root]))
        if branch in branches and branches[branch] != meta:
            raise ValueError("Plusieurs analyses dans un même sous-dossier Bruker : " + branch)
        branches[branch] = meta
    all_names = [item.filename for item in archive.infolist()]

    def branch_of(member: str) -> str:
        parts = member.split("/", common + 1)
        return "/".join(parts[:common + 1]) if len(parts) > common else ""

    # L'archive peut contenir 1700 RMN : choisir directement le préfixe du
    # membre évite une recherche de chaque dossier pour chaque fichier.
    used = {branch_of(name).casefold() for name in all_names
            if branch_of(name) not in branches}
    replacements: dict[str, str] = {}
    for branch in sorted(branches, key=str.casefold):
        parent = branch.rsplit("/", 1)[0] + "/" if "/" in branch else ""
        stem = Path(branches[branch].filename).stem
        number = 1
        while True:
            candidate = parent + stem + (f"__{number}" if number > 1 else "")
            if candidate.casefold() not in used:
                break
            number += 1
        replacements[branch] = candidate
        used.add(candidate.casefold())
    result: dict[str, str] = {}
    pdf_stems: dict[str, str] = {}
    for name in all_names:
        old = branch_of(name)
        if old not in replacements or not name.startswith(old + "/"):
            continue
        new = replacements[old]
        suffix = name[len(old) + 1:]
        old_part = old.rsplit("/", 1)[-1]
        new_part = new.rsplit("/", 1)[-1]
        # Certains exports ont deux dossiers superposés de même nom.
        if suffix.startswith(old_part + "/"):
            suffix = new_part + suffix[len(old_part):]
        result[name] = new + "/" + suffix
        if name.lower().endswith(".pdf"):
            pdf_stems[name] = new_part
    # Garder les fichiers techniques tels quels, et nommer les PDF affichables.
    used_files = {result.get(name, name).casefold() for name in all_names
                  if name not in pdf_stems}
    for old in sorted(pdf_stems, key=str.casefold):
        target = result[old]
        if not re.search(r"/pdata/\d+/[^/]+\.pdf$", target, re.I):
            used_files.add(target.casefold())
            continue
        parent = target.rsplit("/", 1)[0]
        stem = pdf_stems[old]
        count = 1
        while True:
            candidate = parent + "/" + stem + (f"__{count}" if count > 1 else "") + ".pdf"
            if candidate.casefold() not in used_files:
                break
            count += 1
        result[old] = candidate
        used_files.add(candidate.casefold())
    return result


def unique_member_name(original: str, desired: str, used: set[str]) -> str:
    parent = original.rsplit("/", 1)[0] + "/" if "/" in original else ""
    stem = Path(desired).stem
    number = 1
    while True:
        tail = f"{stem}__{number}.zip" if number > 1 else desired
        candidate = parent + tail
        if candidate.casefold() not in used:
            used.add(candidate.casefold())
            return candidate
        number += 1


def inspect_archive(path: Path) -> tuple[str, BrukerName | None, dict[str, str], tuple[str, ...]]:
    with zipfile.ZipFile(path) as archive:
        records = records_in_bruker_zip(archive)
        missing_titles = [p for p in records if not decode_title(archive.read(p))]
        notes = tuple("Nom Bruker vide : identifiant du dossier conservé pour " + p
                      for p in missing_titles)
        direct = set(records.values())
        roots = {path.rsplit("/pdata/", 1)[0].rsplit("/", 1)[0]
                 for path in records}
        if len(direct) == 1 and len(roots) == 1:
            return "single", next(iter(direct)), {}, notes
        if records:
            mapping = raw_folder_mapping(archive, records)
            return "folders", None, mapping, notes
        nested = sorted((item for item in archive.infolist()
                         if not item.is_dir() and item.filename.lower().endswith(".zip")),
                        key=lambda info: info.filename.casefold())
        if not nested:
            raise ValueError("Aucun pdata/.../title ni ZIP Bruker intérieur trouvé.")
        discovered: dict[str, BrukerName] = {}
        notes: list[str] = []
        for info in nested:
            try:
                # Lecture progressive : les gros ZIP intérieurs débordent sur disque.
                with tempfile.SpooledTemporaryFile(max_size=32 * 1024 * 1024) as spool:
                    with archive.open(info) as stream:
                        shutil.copyfileobj(stream, spool, length=1024 * 1024)
                    spool.seek(0)
                    with zipfile.ZipFile(spool) as inner:
                        found = names_in_bruker_zip(inner)
                if len(found) != 1:
                    notes.append(f"Conservé sans renommage (nom ambigu/absent) : {info.filename}")
                    continue
                discovered[info.filename] = next(iter(found))
            except (OSError, RuntimeError, ValueError, zipfile.BadZipFile) as error:
                notes.append(f"Conservé sans renommage : {info.filename} ({error})")
        if not discovered:
            raise ValueError("Aucun ZIP Bruker intérieur avec un nom unique trouvé.")
        used = {item.filename.casefold() for item in archive.infolist()
                if item.filename not in discovered}
        mapping = {old: unique_member_name(old, discovered[old].filename, used)
                   for old in sorted(discovered, key=str.casefold)}
        return "nested", None, mapping, tuple(notes)


def unique_output(base: str, used: set[str]) -> str:
    stem = Path(base).stem
    number = 1
    while True:
        candidate = f"{stem}__{number}.zip" if number > 1 else base
        if candidate.casefold() not in used:
            used.add(candidate.casefold())
            return candidate
        number += 1


def plan(source: Path, output_dir: Path, batch: int = 1,
         batch_size: int = 100) -> tuple[list[Job], list[str], int]:
    if batch < 1 or batch_size < 1:
        raise ValueError("Le numéro et la taille du lot doivent être positifs.")
    source, output_dir = source.resolve(), output_dir.resolve()
    if not source.exists():
        raise ValueError(f"Entrée introuvable : {source}")
    if source.is_file():
        if source.suffix.lower() != ".zip" or batch != 1:
            raise ValueError("Choisir un ZIP et utiliser le lot 1.")
        paths = [source]
    else:
        if source == output_dir:
            raise ValueError("Le dossier de sortie doit être distinct de l'entrée.")
        paths = sorted((p for p in source.rglob("*")
                        if p.is_file() and p.suffix.lower() == ".zip"
                        and output_dir not in p.parents), key=lambda p: str(p).casefold())
    total = len(paths)
    first = (batch - 1) * batch_size
    last = batch * batch_size
    used: set[str] = set()
    jobs: list[Job] = []
    errors: list[str] = []
    # Attribuer les suffixes parmi TOUTES les sources : un doublon du lot 2
    # reçoit __2 même si le lot 1 n'a pas encore été exécuté.
    for index, path in enumerate(paths):
        try:
            kind, name, mapping, notes = inspect_archive(path)
            desired = name.filename if kind == "single" else safe(path.stem, 120) + "_renommes.zip"
            destination = output_dir / unique_output(desired, used)
            if destination == path and (source.is_file() or first <= index < last):
                raise ValueError("Nom de sortie identique au fichier source.")
            if source.is_file() or first <= index < last:
                jobs.append(Job(path, destination, mapping if kind != "single" else None,
                                notes, kind))
        except (OSError, RuntimeError, ValueError, zipfile.BadZipFile) as error:
            if source.is_file() or first <= index < last:
                errors.append(f"{path.name} : {error}")
    return jobs, errors, total


def write_single(source: Path, target: Path) -> None:
    # Le fichier ZIP individuel est copié octet pour octet.
    with source.open("rb") as original, target.open("wb") as new:
        shutil.copyfileobj(original, new, length=1024 * 1024)


def write_master(source: Path, target: Path, renames: dict[str, str],
                 entry_progress: Callable[[int, int], None] | None = None) -> None:
    # On garde toutes les entrées, y compris les archives non reconnues.
    with zipfile.ZipFile(source) as original, zipfile.ZipFile(target, "w",
                                                            allowZip64=True) as new:
        new.comment = original.comment
        total_bytes = sum(item.file_size for item in original.infolist())
        processed = 0
        last_percent = -1
        for old_info in original.infolist():
            info = copy.copy(old_info)
            info.filename = renames.get(old_info.filename, old_info.filename)
            if old_info.is_dir():
                new.writestr(info, b"")
            else:
                with original.open(old_info) as stream, new.open(info, "w",
                                                                force_zip64=True) as output:
                    while True:
                        chunk = stream.read(1024 * 1024)
                        if not chunk:
                            break
                        output.write(chunk)
                        processed += len(chunk)
                        percent = processed * 100 // max(1, total_bytes)
                        if entry_progress and percent != last_percent:
                            entry_progress(processed, total_bytes)
                            last_percent = percent
        if entry_progress:
            entry_progress(total_bytes, total_bytes)


def execute(jobs: list[Job], progress: Callable[[str], None] = print,
            entry_progress: Callable[[int, int], None] | None = None) -> tuple[int, int]:
    done = skipped = 0
    for index, job in enumerate(jobs, 1):
        job.destination.parent.mkdir(parents=True, exist_ok=True)
        if job.destination.exists():
            if not zipfile.is_zipfile(job.destination):
                raise ValueError("Une sortie précédente est incomplète : "
                                 f"{job.destination}. Supprimer ce fichier incomplet "
                                 "ou choisir un autre dossier de sortie.")
            skipped += 1
            progress(f"{index}/{len(jobs)} : déjà présent, conservé : {job.destination.name}")
            continue
        # Le nom .zip définitif n'apparaît qu'après une écriture réussie.
        with tempfile.NamedTemporaryFile(dir=job.destination.parent,
                                         prefix=job.destination.stem + "_",
                                         suffix=".part", delete=False) as handle:
            temporary = Path(handle.name)
        try:
            if job.renamed_members is None:
                write_single(job.source, temporary)
            else:
                write_master(job.source, temporary, job.renamed_members, entry_progress)
            if job.destination.exists():
                raise FileExistsError(f"La sortie vient d'apparaître : {job.destination}")
            temporary.rename(job.destination)
            done += 1
            progress(f"{index}/{len(jobs)} : créé : {job.destination.name}")
        except Exception:
            temporary.unlink(missing_ok=True)
            raise
    return done, skipped


def plan_bruker_folder(source: Path, output_dir: Path) -> FolderJob:
    """Prépare une copie complète d'un dossier de données Bruker non compressé."""
    source, output_dir = source.resolve(), output_dir.resolve()
    if not source.is_dir():
        raise ValueError("Choisir un dossier contenant les fichiers Bruker.")
    if source == output_dir or source in output_dir.parents or output_dir in source.parents:
        raise ValueError("Le dossier de sortie doit être distinct et hors du dossier d'entrée.")

    directories: list[Path] = []
    files: list[Path] = []
    for parent, names, filenames in os.walk(source):
        for name in names:
            path = Path(parent) / name
            if path.is_symlink():
                raise ValueError(f"Lien symbolique non pris en charge : {path}")
            directories.append(path)
        for name in filenames:
            path = Path(parent) / name
            if path.is_symlink():
                raise ValueError(f"Lien symbolique non pris en charge : {path}")
            files.append(path)

    groups: dict[tuple[str, ...], set[BrukerName]] = {}
    notes: list[str] = []
    for path in sorted(files):
        parts = path.relative_to(source).parts
        if (len(parts) < 4 or parts[-1].casefold() != "title" or
                not parts[-2].isdigit() or parts[-3].casefold() != "pdata" or
                not parts[-4].isdigit()):
            continue
        experiment = path.parent.parent.parent
        acqus = experiment / "acqus"
        if not acqus.is_file():
            raise ValueError(f"acqus manquant près de {path}")
        title = decode_title(path.read_bytes())
        root_parts = parts[:-4]
        if not title:
            title = root_parts[-1] if root_parts else source.name
            notes.append(f"Nom Bruker vide : identifiant {title} conservé pour {path}")
        solvent, nucleus = acquisition(acqus.read_bytes())
        groups.setdefault(root_parts, set()).add(BrukerName(title, solvent, nucleus))
    if not groups:
        raise ValueError("Aucun dossier Bruker avec pdata/.../title et acqus trouvé.")
    if any(len(values) != 1 for values in groups.values()):
        raise ValueError("Plusieurs analyses dans un même dossier Bruker : "
                         "renommage du dossier ambigu.")

    roots = sorted(groups)
    branches: dict[tuple[str, ...], BrukerName] = {}
    if len(roots) == 1:
        root = roots[0]
        if not root:
            branches[()] = next(iter(groups[root]))
        else:
            # Une seule RMN dans un dossier enveloppe : garder l'enveloppe.
            level = len(root) - 1
            if level > 0 and root[-1].casefold() == root[-2].casefold():
                level -= 1
            branches[root[:level + 1]] = next(iter(groups[root]))
    else:
        common = 0
        while (all(len(root) > common for root in roots) and
               len({root[common].casefold() for root in roots}) == 1):
            common += 1
        if any(len(root) <= common for root in roots):
            raise ValueError("Dossiers Bruker imbriqués : renommage ambigu.")
        for root in roots:
            branch = root[:common + 1]
            meta = next(iter(groups[root]))
            if branch in branches and branches[branch] != meta:
                raise ValueError("Plusieurs analyses dans un même sous-dossier Bruker : "
                                 "/".join(branch))
            branches[branch] = meta

    existing_dirs = {p.relative_to(source).parts for p in directories}
    used = {tuple(part.casefold() for part in p) for p in existing_dirs
            if p not in branches}
    replacements: dict[tuple[str, ...], str] = {}
    for branch in sorted(branches):
        stem = Path(branches[branch].filename).stem
        count = 1
        while True:
            candidate = stem + (f"__{count}" if count > 1 else "")
            if tuple(part.casefold() for part in branch[:-1] + (candidate,)) not in used:
                break
            count += 1
        replacements[branch] = candidate
        used.add(tuple(part.casefold() for part in branch[:-1] + (candidate,)))

    level = len(next(iter(replacements)))
    def translate(parts: tuple[str, ...]) -> tuple[str, ...]:
        branch = parts[:level]
        replacement = replacements.get(branch)
        if replacement is None:
            return parts
        if not branch:
            return (replacement,) + parts
        suffix = parts[level:]
        if suffix and suffix[0].casefold() == branch[-1].casefold():
            suffix = (replacement,) + suffix[1:]
        return branch[:-1] + (replacement,) + suffix

    directory_targets = [(p, Path(*translate(p.relative_to(source).parts)))
                         for p in directories]
    if () in replacements:
        directory_targets.insert(0, (source, Path(replacements[()])))
    targets: dict[Path, Path] = {}
    used_files = set()
    for file in sorted(files):
        parts = file.relative_to(source).parts
        if (len(parts) >= 3 and parts[-1].lower().endswith(".pdf") and
                parts[-2].isdigit() and parts[-3].casefold() == "pdata"):
            continue
        target = Path(*translate(parts))
        targets[file] = target
        used_files.add(str(target).casefold())
    for file in sorted(files):
        if file in targets:
            continue
        parts = file.relative_to(source).parts
        target = Path(*translate(parts))
        branch = parts[:level]
        if branch in replacements:
            parent = target.parent
            # L'identifiant du dossier Bruker renommé devient aussi celui du PDF.
            stem = replacements[branch]
            count = 1
            while True:
                candidate = parent / (stem + (f"__{count}" if count > 1 else "") + ".pdf")
                if str(candidate).casefold() not in used_files:
                    target = candidate
                    break
                count += 1
        if str(target).casefold() in used_files:
            raise ValueError(f"Deux fichiers porteraient le même nom : {target}")
        targets[file] = target
        used_files.add(str(target).casefold())

    names = [str(path).casefold() for _, path in directory_targets]
    if len(set(names)) != len(names):
        raise ValueError("Deux dossiers auraient le même nom après renommage.")
    if set(names) & used_files:
        raise ValueError("Un fichier et un dossier auraient le même nom après renommage.")
    total_bytes = sum(path.stat().st_size for path in files)
    return FolderJob(source, output_dir, directory_targets,
                     [(file, targets[file]) for file in sorted(files)],
                     len(branches), tuple(notes), total_bytes)


def execute_bruker_folder(job: FolderJob,
                          progress: Callable[[int, int], None] | None = None) -> None:
    destination = job.destination
    if destination.exists() and (not destination.is_dir() or any(destination.iterdir())):
        raise FileExistsError(f"Le dossier de sortie n'est pas vide : {destination}. "
                              "Choisir un dossier vide ou un autre nom.")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=destination.name + "_", suffix=".part",
                                      dir=destination.parent))
    copied = 0
    last_percent = -1
    try:
        for _, relative in job.directories:
            (temporary / relative).mkdir(parents=True, exist_ok=True)
        for original, relative in job.files:
            target = temporary / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            with original.open("rb") as source_file, target.open("wb") as output_file:
                while chunk := source_file.read(1024 * 1024):
                    output_file.write(chunk)
                    copied += len(chunk)
                    percent = copied * 100 // max(1, job.total_bytes)
                    if progress and percent != last_percent:
                        progress(copied, job.total_bytes)
                        last_percent = percent
            shutil.copystat(original, target)
        for original, relative in sorted(job.directories,
                                         key=lambda pair: len(pair[1].parts), reverse=True):
            shutil.copystat(original, temporary / relative)
        if destination.exists():
            if not destination.is_dir() or any(destination.iterdir()):
                raise FileExistsError(f"Le dossier de sortie vient d'être rempli : {destination}")
            destination.rmdir()
        temporary.rename(destination)
        if progress:
            progress(job.total_bytes, job.total_bytes)
    except Exception:
        shutil.rmtree(temporary)
        raise


def cli() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("entree", nargs="?", type=Path,
                        help="ZIP, dossier de ZIP, ou dossier de données Bruker")
    parser.add_argument("-o", "--sortie", type=Path, help="dossier des résultats renommés")
    parser.add_argument("--dossier-bruker", action="store_true",
                        help="copier directement les données Bruker sans ZIP")
    parser.add_argument("--lot", type=int, default=1, help="numéro du lot, à partir de 1")
    parser.add_argument("--taille-lot", type=int, default=100, help="archives par lot")
    parser.add_argument("--appliquer", action="store_true", help="écrire les archives")
    args = parser.parse_args()
    if args.entree is None:
        gui()
        return
    output = args.sortie or args.entree.parent / (
        "Renommes_RMN_Dossiers" if args.dossier_bruker else "Renommes_RMN")
    try:
        if args.dossier_bruker:
            job = plan_bruker_folder(args.entree, output)
            print(f"Spectres renommés : {job.renamed} ; "
                  f"fichiers conservés : {len(job.files)} ; sortie : {job.destination}")
            for note in job.notes[:10]:
                print("À vérifier : " + note)
            if args.appliquer:
                execute_bruker_folder(job)
                print(f"Dossier créé : {job.destination}")
            else:
                print("Aperçu seulement ; ajouter --appliquer pour créer le dossier.")
            return
        jobs, errors, total = plan(args.entree, output, args.lot, args.taille_lot)
        print(f"Archives trouvées : {total} ; prêtes pour ce lot : {len(jobs)}.")
        for job in jobs[:15]:
            extra = (f" ({len(job.renamed_members)} entrées dans des dossiers Bruker renommés)"
                     if job.kind == "folders" else
                     f" ({len(job.renamed_members)} ZIP intérieurs renommés)"
                     if job.kind == "nested" else "")
            print(f"  {job.source.name} -> {job.destination.name}{extra}")
            for note in job.notes[:3]:
                print("    " + note)
        if len(jobs) > 15:
            print(f"  ... et {len(jobs) - 15} autres archives.")
        for issue in errors:
            print("À vérifier : " + issue, file=sys.stderr)
        if args.appliquer:
            completed, skipped = execute(jobs)
            print(f"Terminé : {completed} créé(s), {skipped} déjà présent(s).")
        else:
            print("Aperçu seulement ; ajouter --appliquer pour créer les ZIP.")
        if errors:
            sys.exit(1)
    except (OSError, RuntimeError, ValueError, zipfile.BadZipFile) as error:
        parser.exit(1, f"Erreur : {error}\n")


def gui() -> None:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk

    root = tk.Tk()
    root.title("Renommer les RMN Bruker")
    root.geometry("920x570")
    source = tk.StringVar()
    output = tk.StringVar()
    mode = tk.StringVar(value="zip")
    batch = tk.StringVar(value="1")
    batch_size = tk.StringVar(value="100")
    events: queue.Queue = queue.Queue()
    busy = False
    frame = ttk.Frame(root, padding=16)
    frame.pack(fill="both", expand=True)
    frame.columnconfigure(1, weight=1)
    ttk.Label(frame, text="ZIP ou dossier à traiter").grid(row=0, column=0, sticky="w")
    ttk.Entry(frame, textvariable=source).grid(row=0, column=1, sticky="ew", padx=8)

    def select_file(multiple: bool = False) -> None:
        chosen = filedialog.askopenfilename(filetypes=[("Archives ZIP", "*.zip")])
        if chosen:
            source.set(chosen)
            output.set(str(Path(chosen).parent / "Renommes_RMN"))
            mode.set("zip")
            status.set("Gros ZIP : chaque dossier ou ZIP Bruker sera renommé dans l'archive complète."
                       if multiple else "ZIP individuel : seule la copie de l'archive change de nom.")

    def select_folder(bruker: bool = False) -> None:
        chosen = filedialog.askdirectory()
        if chosen:
            source.set(chosen)
            output.set(str(Path(chosen).parent / (
                "Renommes_RMN_Dossiers" if bruker else "Renommes_RMN")))
            mode.set("bruker" if bruker else "zip")
            status.set("Dossier Bruker : copie intégrale dans le dossier de sortie, "
                       "avec les spectres et les PDF renommés."
                       if bruker else "Dossier de ZIP : traitement des archives par lots.")

    ttk.Button(frame, text="ZIP d'une RMN", command=lambda: select_file(False)).grid(
        row=0, column=2)
    ttk.Button(frame, text="ZIP multi-RMN", command=lambda: select_file(True)).grid(
        row=0, column=3, padx=4)
    ttk.Label(frame, text="Dossier de sortie").grid(row=1, column=0, sticky="w", pady=12)
    ttk.Entry(frame, textvariable=output).grid(row=1, column=1, columnspan=2,
                                               sticky="ew", padx=8)
    ttk.Button(frame, text="Parcourir", command=lambda: output.set(
        filedialog.askdirectory() or output.get())).grid(row=1, column=3)
    ttk.Label(frame, text="Lot nº (dossier de ZIP seulement)").grid(row=2, column=0, sticky="w")
    ttk.Entry(frame, textvariable=batch, width=7).grid(row=2, column=1, sticky="w", padx=8)
    ttk.Label(frame, text="Archives par lot").grid(row=2, column=2, sticky="e")
    ttk.Entry(frame, textvariable=batch_size, width=7).grid(row=2, column=3, sticky="w")
    log = tk.Text(frame, height=15, wrap="word", state="disabled")
    log.grid(row=5, column=0, columnspan=4, sticky="nsew", pady=10)
    frame.rowconfigure(5, weight=1)
    status = tk.StringVar(value="Choisir un ZIP. Il sera copié en entier sous son nouveau nom.")
    ttk.Label(frame, textvariable=status, wraplength=800).grid(
        row=6, column=0, columnspan=4, sticky="w")
    progress_bar = ttk.Progressbar(frame, mode="indeterminate")
    progress_bar.grid(row=7, column=0, columnspan=4, sticky="ew", pady=8)

    def add_line(line: str) -> None:
        log.configure(state="normal")
        log.insert("end", line + "\n")
        log.see("end")
        log.configure(state="disabled")

    def begin(apply: bool) -> None:
        nonlocal busy
        if busy:
            return
        try:
            src, dst = Path(source.get()), Path(output.get())
            number, size = int(batch.get()), int(batch_size.get())
            if not source.get() or not output.get():
                raise ValueError("Choisir une entrée et un dossier de sortie.")
            selected_mode = mode.get()
        except ValueError as error:
            messagebox.showerror("Entrée incorrecte", str(error))
            return
        busy = True
        status.set("Analyse / copie en cours…")
        progress_bar.configure(mode="indeterminate", value=0)
        progress_bar.start(12)

        def worker() -> None:
            try:
                if selected_mode == "bruker":
                    job = plan_bruker_folder(src, dst)
                    events.put(("line", f"{job.renamed} spectre(s) renommé(s), "
                                        f"{len(job.files)} fichier(s) copiés."))
                    events.put(("line", f"Entrée : {job.source}"))
                    events.put(("line", f"Sortie : {job.destination}"))
                    for note in job.notes[:20]:
                        events.put(("line", "À vérifier : " + note))
                    if apply:
                        execute_bruker_folder(
                            job, lambda copied, total:
                            events.put(("progress", (copied, total))))
                        events.put(("folder_finished", (job.renamed, str(job.destination))))
                    else:
                        events.put(("done", "Aperçu terminé. Cliquer sur Créer la sortie "
                                            "pour copier le dossier Bruker."))
                    return
                jobs, errors, total = plan(src, dst, number, size)
                events.put(("line", f"{total} archive(s) trouvée(s) ; "
                                    f"{len(jobs)} dans ce lot ; {len(errors)} à vérifier."))
                for job in jobs[:20]:
                    extra = (f" ({len(job.renamed_members)} entrées dans des dossiers renommés)"
                             if job.kind == "folders" else
                             f" ({len(job.renamed_members)} ZIP intérieurs renommés)"
                             if job.kind == "nested" else "")
                    events.put(("line", f"{job.source.name} → {job.destination.name}{extra}"))
                    for note in job.notes[:3]:
                        events.put(("line", "  " + note))
                if len(jobs) > 20:
                    events.put(("line", f"… et {len(jobs) - 20} autres."))
                for issue in errors[:20]:
                    events.put(("line", "À vérifier : " + issue))
                if apply:
                    if not jobs and errors:
                        events.put(("error", "\n".join(errors[:10])))
                        return
                    created, skipped = execute(
                        jobs,
                        lambda message: events.put(("line", message)),
                        lambda copied, total: events.put(("progress", (copied, total))),
                    )
                    paths = [str(job.destination) for job in jobs]
                    events.put(("finished", (f"Terminé : {created} ZIP créé(s), "
                                             f"{skipped} déjà présent(s), {len(errors)} à vérifier.",
                                             paths, skipped)))
                else:
                    events.put(("done", "Aperçu terminé. Cliquer sur Créer les ZIP pour enregistrer."))
            except Exception as error:
                events.put(("error", str(error)))
        threading.Thread(target=worker, daemon=True).start()

    def poll() -> None:
        nonlocal busy
        try:
            while True:
                kind, message = events.get_nowait()
                if kind == "line":
                    add_line(message)
                elif kind == "progress":
                    copied, total = message
                    percent = min(100, round(100 * copied / max(total, 1)))
                    progress_bar.stop()
                    progress_bar.configure(mode="determinate", maximum=100, value=percent)
                    operation = "Copie du dossier" if mode.get() == "bruker" else "Écriture du ZIP"
                    status.set(f"{operation} : {percent} % — "
                               f"{copied / 1048576:.0f} / {total / 1048576:.0f} Mio")
                else:
                    busy = False
                    progress_bar.stop()
                    if kind == "finished":
                        summary, paths, skipped = message
                        status.set(summary)
                        progress_bar.configure(mode="determinate", maximum=100, value=100)
                        if paths:
                            add_line("Emplacement exact du résultat :")
                            for path in paths[:20]:
                                add_line("  " + path)
                            heading = "ZIP déjà présent" if skipped == len(paths) else "ZIP créé"
                            messagebox.showinfo(heading, summary + "\n\nRésultat :\n" +
                                                "\n".join(paths[:5]) +
                                                ("\n…" if len(paths) > 5 else ""))
                    elif kind == "folder_finished":
                        count, path = message
                        summary = f"Terminé : {count} spectre(s) renommé(s)."
                        status.set(summary)
                        progress_bar.configure(mode="determinate", maximum=100, value=100)
                        add_line("Dossier créé : " + path)
                        messagebox.showinfo("Dossier créé", summary + "\n\nRésultat :\n" + path)
                    else:
                        status.set(message)
                    if kind == "error":
                        messagebox.showerror("Erreur", message)
        except queue.Empty:
            pass
        root.after(100, poll)

    ttk.Button(frame, text="Dossier de ZIP", command=lambda: select_folder(False)).grid(
        row=3, column=0, sticky="w", pady=12)
    ttk.Button(frame, text="Dossier Bruker (sans ZIP)",
               command=lambda: select_folder(True)).grid(
        row=3, column=1, sticky="w", pady=12)
    ttk.Button(frame, text="Voir les noms", command=lambda: begin(False)).grid(
        row=4, column=1, sticky="w", pady=12)
    ttk.Button(frame, text="Créer la sortie", command=lambda: begin(True)).grid(
        row=4, column=2, columnspan=2, sticky="e", pady=12)
    root.after(100, poll)
    root.mainloop()


if __name__ == "__main__":
    cli()
