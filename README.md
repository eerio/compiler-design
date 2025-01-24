# compiler-design
Code for the compiler design course @ MIMUW 2023/2024

autor: Pawel Balawender
indeks: 429141

instrukcje uruchamiania
```
gcc -o driver test-tmpfile/driver.c
mkdir test
cd test
cp -r ../driver ../lattests ../mrjp-tests ../pb429141.tgz ../test.sh .
git clone https://github.com/varqox/mrjp-tests.git varqox/mrjp-tests
./driver bash test.sh
```

compiled using:
ghc   9.0.2
