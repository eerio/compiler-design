# pack the important files into a .tgz file

rm -r test
mv README.md README.md2
mv README-oficjalne.md README.md
tar -czf pb429141.tgz src lib Lattec.cabal Makefile README.md  Latte/Latte.cf cabal.project LICENSE.txt
mv README.md README-oficjalne.md
mv README.md2 README.md
mkdir test
mv pb429141.tgz test
