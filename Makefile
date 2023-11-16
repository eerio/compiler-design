GRAMMAR_PATH = Latte

GRAMMAR_FILES = Abs.hs Print.hs Lex.x Par.y Test.hs ErrM.hs Skel.hs

GRAMMAR_FILES_PATH = $(addprefix $(GRAMMAR_PATH)/, $(GRAMMAR_FILES))

.PHONY: all clean
all: latc

latc: $(GRAMMAR_FILES_PATH) src/Main.hs
	cabal build
	cp ./dist-newstyle/build/x86_64-linux/ghc-8.8.4/Lattec-1.0/x/latc/build/latc/latc .

$(GRAMMAR_FILES_PATH): $(GRAMMAR_PATH)/Latte.cf
	bnfc --haskell --functor Latte/Latte.cf -d