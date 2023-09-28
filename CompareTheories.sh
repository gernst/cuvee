#!/usr/bin/bash

# https://stackoverflow.com/questions/6569478/detect-if-executable-file-is-on-users-path

bloop=$(which bloop)
if [ -x "$bloop" ]
then
    $bloop run cuvee -m cuvee.CompareTheories -- $@
else
    echo "please install bloop and set up the project"
fi