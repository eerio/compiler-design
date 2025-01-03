GRAMMAR_PATH = Latte

GRAMMAR_FILES = Abs.hs Print.hs Lex.x Par.y Test.hs ErrM.hs Skel.hs Doc.txt

GRAMMAR_FILES_PATH = $(addprefix $(GRAMMAR_PATH)/, $(GRAMMAR_FILES))

.PHONY: all clean
all: latc lib/runtime.bc

clean:
	rm -rf $(GRAMMAR_FILES_PATH) $(addsuffix .bak, $(GRAMMAR_FILES_PATH))

lib/runtime.bc: lib/runtime.c
	clang -emit-llvm -c -o lib/runtime.bc lib/runtime.c

latc: $(GRAMMAR_FILES_PATH) src/Main.hs Makefile src/TypeChecker.hs src/BackendLLVM.hs
	cabal install --overwrite-policy=always --installdir=.

$(GRAMMAR_FILES_PATH): $(GRAMMAR_PATH)/Latte.cf
	bnfc --haskell --functor Latte/Latte.cf -d
