rm -f "$1".ll "$1".bc
./latc "$1".lat
if [ $? -ne 0 ]; then
  echo "failed!"
  exit
fi
if [ -e "$1".input ]; then
  lli "$1".bc <"$1".input 2>/dev/null
else
  lli "$1".bc 2>/dev/null
fi
if [ $? -ne 0 ]; then
  echo "failed!"
  exit
fi
echo "done"
cat "$1".output
echo "done expected"
