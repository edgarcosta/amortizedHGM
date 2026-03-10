#!/usr/bin/env python
## -*- encoding: utf-8 -*-

from setuptools import setup
from setuptools.extension import Extension
from Cython.Build import cythonize as cython_cythonize

try:
    from sage.config import get_include_dirs
    sage_include_directories = lambda: [str(p) for p in get_include_dirs()]
except ImportError:
    from sage.env import sage_include_directories

try:
    from sage.misc.package_dir import cython_namespace_package_support
    def cythonize(*args, **kwargs):
        with cython_namespace_package_support():
            return cython_cythonize(*args, **kwargs)
except ImportError:
    cythonize = cython_cythonize

hgm_misc = Extension(
    "amortizedHGM.hgm_misc",
    language="cython",
    sources=[
        "amortizedHGM/hgm_misc.pyx"
    ],
    include_dirs=sage_include_directories(),
)

setup(
    ext_modules=cythonize([hgm_misc], include_path=sage_include_directories()),
)
