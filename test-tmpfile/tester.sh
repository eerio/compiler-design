#!/bin/bash

# Ensure that TEMP_FILE_FD is set
if [ -z "$TEMP_FILE_FD" ]; then
  echo "Error: TEMP_FILE_FD is not set"
  exit 1
fi

# Use the file descriptor passed as an environment variable
echo "Using file descriptor: $TEMP_FILE_FD"

# Write to the file descriptor using /dev/fd/$TEMP_FILE_FD
echo "This is a test message from tester.sh" > /dev/fd/$TEMP_FILE_FD

# Read from the file descriptor using /dev/fd/$TEMP_FILE_FD
echo "Reading from file descriptor $TEMP_FILE_FD"
cat /dev/fd/$TEMP_FILE_FD
