# pack the important files into a .tgz file

rm -r test
tar -czf pb429141.tgz src lib Lattec.cabal Makefile README.md  Latte/Latte.cf cabal.project LICENSE.txt
mkdir test
mv pb429141.tgz test