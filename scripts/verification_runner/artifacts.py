"""Detach private build artifacts before strict implementation identity capture."""
import hashlib
import os
from pathlib import Path
import shutil
import tempfile

MARKER = '.verity-private-build'


def binary_artifact(path):
    return (path.suffix in ('.olean', '.ilean', '.so', '.dylib', '.a')
            or path.name.endswith(('.olean.private', '.olean.server')))


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(chunk)
    return value.digest()


def detach(path):
    """Copy bytes and metadata, checking for concurrent content changes before replacement."""
    if path.is_symlink():
        raise RuntimeError(f'Private build artifact is a symlink: {path}')
    before = path.stat()
    if before.st_nlink <= 1:
        return False
    fd, name = tempfile.mkstemp(prefix='.private-artifact-', dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, 'wb') as target, path.open('rb') as source:
            shutil.copyfileobj(source, target)
        copied = digest(temporary)
        if copied != digest(path):
            raise RuntimeError(f'Artifact changed while copying: {path}')
        current = path.stat()
        # ctime/link count can change when another checkout materializes the same CAS blob.
        fields = ('st_dev', 'st_ino', 'st_size', 'st_mtime_ns')
        if any(getattr(current, key) != getattr(before, key) for key in fields):
            raise RuntimeError(f'Artifact replaced while copying: {path}')
        shutil.copystat(path, temporary)
        temporary.replace(path)
        if path.stat().st_nlink != 1 or digest(path) != copied:
            raise RuntimeError(f'Artifact isolation failed: {path}')
        return True
    finally:
        temporary.unlink(missing_ok=True)


def isolate_private_build(project):
    """Only mutate explicitly private snapshots, never the parent cache or packages."""
    project = Path(project).resolve()
    if not (project / '.lake' / MARKER).is_file():
        return 0
    lib = project / '.lake/build/lib'
    if not lib.resolve().is_relative_to(project):
        raise RuntimeError('Private build resolves outside its snapshot')
    count = 0
    for current, directories, files in os.walk(lib, followlinks=False):
        if any((Path(current) / name).is_symlink() for name in directories):
            raise RuntimeError('Private build contains a symlinked directory')
        for name in files:
            path = Path(current) / name
            if binary_artifact(path):
                count += detach(path)
    return count
