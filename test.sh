#!/bin/bash

RT=mrjp-tests
RT2=lattests
BIN=./latc

# "$RT2"/extensions  "$RT"/gr5 
# for filename in $(find "$RT"/good "$RT2"/good -name "*.lat"); do
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
      "$filename" \
      1> >(cat - >&${fd_outw}) \
      2> >(cat - >&${fd_errw})

  # check exit code and if first line of stderr is "OK":
  if [ $? -ne 0 ] || [ "`head -n 1 <&${fd_errr}`" != "OK" ]; then
    echo "$filename: failed!"
    cat <&${fd_errr2}
    cat <&${fd_outr}
    exit
  else
    echo "$filename: correct"
  fi

  exec {fd_outw}>&-
  exec {fd_outr}<&-
  exec {fd_outr2}<&-
  exec {fd_errw}>&-
  exec {fd_errr}<&-
  exec {fd_errr2}<&-
done

for filename in $(find "$RT2"/bad "$RT/bad/semantic" ! -path "$RT/weird_bad" -name "*.lat"); do
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
      "$filename" \
      1> >(cat - >&${fd_outw}) \
      2> >(cat - >&${fd_errw})
  
  # check exit code
  if [ $? -ne 0 ] && [ "`head -n 1 <&${fd_errr}`" = "ERROR" ]; then
    echo "$filename: correct"
  else
    echo "$filename: failed!"
    cat <&${fd_errr2}
    cat <&${fd_outr}
    exit
  fi

  exec {fd_outw}>&-
  exec {fd_outr}<&-
  exec {fd_outr2}<&-
  exec {fd_errw}>&-
  exec {fd_errr}<&-
  exec {fd_errr2}<&-
done

for filename in $(find "tests-pretty-exceptions" -name "*.lat"); do
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
      "$filename" \
      1> >(cat - >&${fd_outw}) \
      2> >(cat - >&${fd_errw})

  # check exit code
  if [ $? -eq 0 ]; then
    echo "$filename: failed!"
    cat <&${fd_errr}
    cat <&${fd_outr}
    exit
  fi

  cmp <(cat <&${fd_errr}) "${filename%.lat}.err"
  if [ $? -ne 0 ]; then
    echo "$filename: failed! (actual message above, expected below)"
    cat <&${fd_errr2}
    cat "${filename%.lat}.err"
    exit
  fi
  
  echo "$filename: correct"

  exec {fd_outw}>&-
  exec {fd_outr}<&-
  exec {fd_outr2}<&-
  exec {fd_errw}>&-
  exec {fd_errr}<&-
  exec {fd_errr2}<&-
done

