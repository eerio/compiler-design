#!/bin/bash

RT=mrjp-tests
RT2=lattests
BIN=./latc


for filename in $(find "$RT"/good "$RT2"/good ! -path "$RT/good/virtual/*" ! -path "$RT/good/arrays/*" -name "*.lat"); do
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

  # check exit code and if first line of stderr is "OK":
  if [ $? -ne 0 ] || [ "`head -n 1 <&${fd_errr2}`" != "OK" ]; then
    echo "$filename: failed!"
    cat <&${fd_errr}
    cat <&${fd_outr}
    exit
  else
    echo "$filename: correct"
  fi
done

for filename in $(find "$RT2"/bad "$RT/bad/semantic" -name "*.lat"); do
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
  if [ $? -ne 0 ] && [ "`head -n 1 <&${fd_errr2}`" = "ERROR" ]; then
    echo "$filename: correct"
  else
    echo "$filename: failed!"
    cat <&${fd_errr}
    cat <&${fd_outr}
    break
  fi
done

