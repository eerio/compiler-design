#!/bin/bash

RT=mrjp-tests
BIN=./latc


for filename in $(find "$RT"/good -name "*.lat"); do
  [ -e "$filename" ] || continue
  # create temporary files for examination and a pair of fds for each of them
  # that's because we want to read these files and bash doesn't provide a way
  # to seek in file, so after a write we are unable to go back if we only create
  # one fd
  temp_out=$(mktemp)
  temp_err=$(mktemp)
  exec {fd_outw}>"$temp_out"
  exec {fd_outr}<"$temp_out"
  exec {fd_outr2}<"$temp_out"
  exec {fd_errw}>"$temp_err"
  exec {fd_errr}<"$temp_err"
  exec {fd_errr2}<"$temp_err"
  rm "$temp_out"
  rm "$temp_err"

  # execute, save stdout and stderr to temp files for verification
  $BIN \
      < "$filename" \
      1> >(cat - >&${fd_outw}) \
      2> >(cat - >&${fd_errw})

  # check exit code
  if [ $? -ne 0 ]; then
    echo "$filename: failed!"
    # print stderr
    cat <&${fd_errr}
    # print stdout
    cat <&${fd_outr}
    break
  else
    echo "$filename: correct"
  fi
done

# for filename in $(find "$RT"/bad -name "*.lat"); do
#   [ -e "$filename" ] || continue
#   if $BIN "$filename" >/dev/null ; then
#     echo "$filename failed!"
#   else
#     echo "$filename: correct"
#     break
#   fi
# done

