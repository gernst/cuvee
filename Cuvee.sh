#!/usr/bin/bash

# https://stackoverflow.com/questions/6569478/detect-if-executable-file-is-on-users-path

bloop=$(which bloop)
if [ -x "$bloop" ]
then
    $bloop run cuvee -- $@
else
    ./mill --disable-ticker cuvee.run $@
fi