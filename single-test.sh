rm -f "$1".ll "$1".bc
./latc "$1".lat
if [ $? -ne 0 ]; then
  echo "failed!"
  exit
fi
if [ -e "$1".input ]; then
  lli "$1".bc <"$1".input
else
  lli "$1".bc
fi
if [ $? -ne 0 ]; then
  echo "failed!"
  exit
fi
echo "done"
cat "$1".output
echo "done expected"
