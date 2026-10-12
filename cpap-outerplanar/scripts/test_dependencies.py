"""Tests for the resolution of dependency directories from `lake-manifest.json`."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from dependencies import dependency_dir

MANIFEST = {
    "version": "1.2.0",
    "packagesDir": ".lake/packages",
    "packages": [
        {"type": "path", "scope": "", "name": "cpap-np-hardness", "manifestFile": "lake-manifest.json",
         "inherited": False, "dir": "../cpap-np-hardness", "configFile": "lakefile.toml"},
        {"url": "https://example.org/section8.git", "type": "git", "subDir": None, "scope": "",
         "rev": "c090168e8f0f8fb2410000d034d3d4f333309d84", "name": "«cpap-minor-free»",
         "manifestFile": "lake-manifest.json", "inputRev": "c090168e8f0f8fb2410000d034d3d4f333309d84",
         "inherited": False, "configFile": "lakefile.toml"},
    ],
    "name": "«cpap-outerplanar»",
    "lakeDir": ".lake",
}


class DependencyDirTests(unittest.TestCase):
    def test_path_and_git_layouts(self):
        with TemporaryDirectory() as directory:
            root = Path(directory) / "cpap-outerplanar"
            root.mkdir()
            (root / "lake-manifest.json").write_text(json.dumps(MANIFEST))
            self.assertEqual(dependency_dir(root, "cpap-np-hardness"),
                             (Path(directory) / "cpap-np-hardness").resolve())
            self.assertEqual(dependency_dir(root, "cpap-minor-free"),
                             root / ".lake/packages/cpap-minor-free")
            with self.assertRaises(ValueError):
                dependency_dir(root, "missing")

    def test_this_package(self):
        root = Path(__file__).resolve().parents[1]
        for name in ("np-completeness", "cpap-np-hardness", "cpap-minor-free", "mathlib"):
            self.assertTrue(str(dependency_dir(root, name)))


if __name__ == '__main__':
    unittest.main()
