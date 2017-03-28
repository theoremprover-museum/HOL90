#!/bin/sh
#
# This is a front-end script for building the HOL system. It provides 
# parameters to `make' that appear not to be computable in
# the Makefile (at least not in a way that works for all architectures).

# Default parameters
#
HOL_DIR=`(cd ..; /bin/pwd)`
ARCH=`../tools/architecture`

perl -pe "s|__HOLdir__|$HOL_DIR/|; s|__arch__|$ARCH|;" < SysParams.sml.template\
> SysParams.sml
# Run `make'
make -f Makefiles/Makefile ARCH=$ARCH HOL_DIR=$HOL_DIR "$@"
