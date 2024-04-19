#!/bin/bash

# Copyright 2024 ZhengPu Shi
# This file is part of CoqMatrix. It is distributed under the MIT
# "expat license". You should have recieved a LICENSE file with it.

# Why need this script? we need to fix something to compile the Ocaml program
# 1. Issues when extract Ocaml program
# a. two functions about "coq_R" need to be masked: coqRasbst, coq_Rrepr
# b. the parameter in definition of "predP" is not match
# 2. there is a type mismatch for "coq_X" and "float" when compiling, although there
#    is no problem in REPL. Now, we find that concate matrix.ml and test.ml will solve
#    the compile problem.
# 3. remove "#use" indicators in the top of "test.ml" file.

# What's done?
# 1. create new directory "build", then change to this directory.
# 2. copy matrix.ml and test.ml to this directory.
# 3. fix some code in matrix.ml.
# 4. remove some header lines of test.ml, then append it to matrix.ml
# 5. use ocamlfind to compile, because we need third-party library such as unix.

# welcome
echo "Compile preparing..."

# change to directory where this script is located
cd `dirname $0`
dir=`pwd`

# create directory for building
mkdir -p build

# change to this directory
cd build

# copy files needed
cp ../matrix.mli ./
cp ../matrix.ml ./
cp ../test.ml ./
cp ../Makefile ./

sed -i 's/coq_Rabst : cReal -> coq_R/coq_Rabst : __/' matrix.mli
sed -i 's/coq_Rrepr : coq_R -> cReal/coq_Rrepr : __/' matrix.mli
sed -i 's/coq_Rabst : cReal -> coq_R/coq_Rabst : __/' matrix.ml
sed -i 's/coq_Rrepr : coq_R -> cReal/coq_Rrepr : __/' matrix.ml
# sed -i "s/simplPred (fun _ -> true)/fun (_:'a1) -> true/" matrix.ml
sed -i 's/^#.*//' test.ml

# concate two files
cat test.ml >> matrix.ml

# compile
make

# copy output to parent directory
cp matrix ../

# remove intermediate files and directories
cd ../
rm build -r

# notification
echo 'Compile finished. output file is "matrix"'
