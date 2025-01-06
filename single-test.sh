rm -f "$1".ll "$1".bc && ./latc "$1".lat && lli "$1".bc && echo "done" && cat "$1".output && echo "done expected"
