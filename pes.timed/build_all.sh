#!/bin/sh

#Shell File to compile pes.timed.
#Uses the various makefiles

make

#This Code Assumes that we are in the directory of the original Makefile
cd Examples/ExampleGenerators
make
cd ../..
# Am now back in the original directory

