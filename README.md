# TimeSolver

This program is a Model Checker for timed automata that uses pes (predicate equation systems).

## Contents

* [Brief Program Description](#brief-program-description)
* [Installing/Compiling](#installing-compiling)
* [Running the Program](#running-the-program)
* [Generating Examples](#generating-examples)
* [Notes](#notes)

## Authors

Written by Peter Fontana (pfontana@cs.umd.edu), Rance Cleaveland (rance@cs.umd.edu) Jeroen Keiren (Jeroen.Keiren@ou.nl). Based on earlier work by Dezhuang Zhang.

## Getting the source

You can obtain the source of the development version from Bitbucket:

```
git@github.com:jkeiren/TimeSolver.git
```

## Installing/Compiling

The build system uses [CMake](https://cmake.org/). The minimal required version is CMake 3.5. If you want to be able to generate Doxygen documentation, you should use version 3.9 or newer. If you want to be able to run the unit tests, version 3.10 is required.

### Building
To build, execute the following from the root of your working copy.

```
mkdir build
cd build
cmake ..
make
```

This will create a default build of timesolver. If you want to use multiple threads when building, use `make -jN` with `N` the number of threads.

### Installing
You can install the tool by executing, from the `build` directory

```
make install
```

By default, this will install to `/usr/local/bin`. If you want to install to another location, execute the following from your `build` directory before make install (or when executing the intial `cmake` command)

```
cmake .. -DCMAKE_INSTALL_PREFIX=/path/to/prefix
```

### Cleaning

If you followed the instructions above, you can clean up by doing `rm -r build` from the root of your repository.

### Generating source code documentation

You can generate source code documentation using `make doxygen`. The output will be generated in the directory `build/pes.timed/html`.

### Dependencies

No additional libraries are needed. For testing, googletest is used, but this is downloaded on-demand.

## Testing

Unit tests and tool tests are included in the build system. All tests can be run from the `build` directory in which you built the tool, by executing

```
ctest -jN
```
where `N` is again the number of threads to execute.

If you only want to run the examples, you can use
```
ctest -jN -R tooltest
```

If you want to run all but the tooltests (i.e. the unit tests), you can use

```
ctest -jN -E tooltest
```

## Running the Program

The executable program is named `timesolver-ta`.

To run, use `timesolver-ta <exampleFile>`

Example files are included in the `example` directory 

## Generating Examples

*This section is outdated, and needs to be updated*.

Running `./build_all.sh` will compile the program and the example-generating programs.

Most examples are already there.  Some are program-generated.  To compile the programs to generate examples, either run "make" in each directory (with the desired makefile), or in the regular directory run `./build_all.sh`  This will compile the original program and the example-generating programs.

Then, run each program and provide as a parameter the number of processes.  This will then write to standard output the generated example.  It is recommended to redirect the output to a file.

Some folders will have various examples.

## Notes

No additional Notes.
