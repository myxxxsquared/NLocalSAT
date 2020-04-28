from distutils.core import setup, Extension

import os
import numpy


if 'DEBUG' in os.environ and os.environ['DEBUG']:
    DEBUG = True
else:
    DEBUG = False

envpath = os.environ["CONDA_PREFIX"]
numpypath = numpy.__path__[0]

sources = [
    os.path.join("src", f)
    for f in filter(
        lambda x: x.endswith(".cpp") and x != "generator_main.cpp", os.listdir("src")
    )
]

module = Extension(
    "_satgenerator",
    sources=sources,
    include_dirs=[
        os.path.join(envpath, "include"),
        os.path.join(numpypath, "core/include"),
    ],
    library_dirs=[os.path.join(envpath, "lib")],
    libraries=[],
    depends=["opencv", "numpy"],
    extra_compile_args=[("-O0" if DEBUG else "-O3"), "-ggdb", "-std=gnu++11", "-Wall"],
    extra_link_args=[("-O0" if DEBUG else "-O3"), "-ggdb", "-Wall"],
    define_macros=([("SAT_DEBUG", "")] if DEBUG else []),
)

setup(
    name="_satgenerator",
    version="1.0",
    description="_satgenerator",
    ext_modules=[module],
)
