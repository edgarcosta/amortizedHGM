#!/usr/bin/env python
## -*- encoding: utf-8 -*-

import os
import sys
from setuptools import setup
from codecs import open  # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand  # for tests
from setuptools.extension import Extension
from sage.env import sage_include_directories
from Cython.Build import cythonize

# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename, encoding="utf-8") as f:
        return f.read()


# For the tests
class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --force-lib amortizedHGM")
        if errno != 0:
            sys.exit(1)


cythonize_dir = "build"




hgm_misc = Extension(
    "amortizedHGM.hgm_misc",
    language="cython",
    sources=[
        "amortizedHGM/hgm_misc.pyx"
    ],
    include_dirs=sage_include_directories(),
)

setup(
    name="amortizedHGM",
    author="Edgar Costa, Kiran Kedlaya and David Roe",
    author_email="edgarc@mit.edu",
    url="https://github.com/edgarcosta/amortizedHGM",
    license="GNU General Public License, version 3",
    description='Sage code supporting "Hypergeometric L-functions in average polynomial time" by Edgar Costa, Kiran Kedlaya and David Roe',
    long_description=readfile("README.md"),  # get the long description from the README
    version=readfile("VERSION").strip(),  # the VERSION file is shared with the documentation
    classifiers=[
        # How mature is this project? Common values are
        #   3 - Alpha
        #   4 - Beta
        #   5 - Production/Stable
        "Development Status :: 4 - Beta",
        "Intended Audience :: Science/Research",
        "Topic :: Scientific/Engineering :: Mathematics",
        "License :: OSI Approved :: GNU General Public License, version 3",
        "Programming Language :: Python :: 3.7",
    ],  # classifiers list: https://pypi.python.org/pypi?%3Aaction=list_classifiers
    keywords="sagemath amortizedHGM",
    setup_requires=[
        "cython",
        "sagemath",
    ],  # currently useless, see https://www.python.org/dev/peps/pep-0518/
    install_requires=[
        "cython",
        "sagemath",
        "sphinx",
        "pyrforest @ git+https://github.com/edgarcosta/pyrforest.git",
    ],
    packages=["amortizedHGM"],
    include_package_data=False,
    ext_modules=cythonize([hgm_misc]),
    cmdclass={"test": SageTest}  # adding a special setup command for tests
    # ext_modules = extensions,
    # cmdclass = {'test': SageTest, 'build_ext': Cython.Build.build_ext} # adding a special setup command for tests and build_ext
)
