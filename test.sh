#!/bin/bash

RT=mrjp-tests
RT2=lattests
BIN=./latc

if [ -z "$TEMP_FILE_FD_1" ] || [ -z "$TEMP_FILE_FD_2" ] || [ -z "$TEMP_FILE_FD_3" ]; then
  echo "Error: TEMP_FILE_FD_1, TEMP_FILE_FD_2 or TEMP_FILE_FD_3 is not set"
  exit 1
fi
temp_out=/dev/fd/$TEMP_FILE_FD_1
temp_err=/dev/fd/$TEMP_FILE_FD_2
temp_out_exec=/dev/fd/$TEMP_FILE_FD_3

# "$RT2"/extensions  "$RT"/gr5
# for filename in $(find "$RT"/good "$RT2"/good -name "*.lat"); do
# for filename in $(find "$RT"/good "$RT2"/good ! -path "$RT/good/virtual/*" ! -path "$RT/good/arrays/*" -name "*.lat"); do
for filename in $(find "$RT2"/good/ "$RT"/good/basic ! -path "$RT/good/virtual/*" ! -path "$RT/good/arrays/*" ! -path "$RT2"/good/daria-error.lat -name "*.lat"); do
  [ -e "$filename" ] || continue
  echo -n "$filename"

  # execute, save stdout and stderr to temp files for verification
  rm -f "${filename%.lat}.ll" "${filename%.lat}.bc"
  $BIN "$filename" 1> $temp_out 2> $temp_err

  if [ $? -ne 0 ] || [ "`head -n 1 $temp_err`" != "OK" ]; then
    echo ": failed!"
    cat $temp_err
    cat $temp_out
    exit
  else
    if [ -e "${filename%.lat}.input" ]; then
      lli "${filename%.lat}.bc" 1>$temp_out_exec <"${filename%.lat}.input"
    else
      lli "${filename%.lat}.bc" 1>$temp_out_exec
    fi

    if [ $? -ne 0 ]; then
      echo ": failed! (non-zero exit code)"
      exit
    fi

    cmp -s $temp_out_exec "${filename%.lat}.output"
    if [ $? -ne 0 ]; then
      echo ": failed! (actual output above, expected below)"
      cat $temp_out_exec
      echo "expected:"
      cat "${filename%.lat}.output"
      exit
    fi
    echo ": correct"
  fi

  >| $temp_out
  >| $temp_err
  >| $temp_out_exec
done

for filename in $(find "varqox/mrjp-tests/bad" "$RT2"/bad "$RT/bad/semantic" ! -path "$RT/weird_bad" -name "*.lat"); do
  [ -e "$filename" ] || continue
  echo -n "$filename"

  # execute, save stdout and stderr to temp files for verification
  $BIN "$filename" 1> $temp_out 2> $temp_err
  
  # check exit code
  if [ $? -ne 0 ] && [ "`head -n 1 $temp_err`" = "ERROR" ]; then
    echo ": correct"
  else
    echo ": failed!"
    cat $temp_err
    cat $temp_out
    exit
  fi

  >| $temp_out
  >| $temp_err
done

for filename in $(find lattests mrjp-tests varqox/mrjp-tests ! -path "varqox/mrjp-tests/good_weird/*" ! -path "varqox/mrjp-tests/bad/*" ! -path "mrjp-tests/bad/*" ! -path "mrjp-tests/weird_bad/*" ! -path "mrjp-tests/weird_good/*" ! -path "lattests/bad/*" -name '*.lat'); do
  [ -e "$filename" ] || continue
  echo -n "$filename"

  # execute, save stdout and stderr to temp files for verification
  $BIN "$filename" 1> $temp_out 2> $temp_err
  
  # check if first line of stderr is "OK" (frontend accepted the file)
  # ignore exit code, as backend might stil fail
  if [ "`head -n 1 $temp_err`" != "OK" ]; then
    echo ": failed!"
    cat $temp_err
    cat $temp_out
    exit
  else
    echo ": correct"
  fi

  >| $temp_out
  >| $temp_err
done

for filename in $(find "tests-pretty-exceptions" -name "*.lat"); do
  [ -e "$filename" ] || continue
  echo -n "$filename"

  $BIN "$filename" 1> $temp_out 2> $temp_err

  if [ $? -eq 0 ]; then
    echo ": failed!"
    cat $temp_err
    cat $temp_out
    exit
  fi

  cmp $temp_err "${filename%.lat}.err"
  if [ $? -ne 0 ]; then
    echo ": failed! (actual message above, expected below)"
    cat $temp_err
    cat "${filename%.lat}.err"
    exit
  fi
  
  echo ": correct"
  >| $temp_out
  >| $temp_err
done

