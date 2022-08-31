SHELL      := bash
TARGET     := Main.native
JUNAC      := junac
DIRS       := kremlin,alphalib
OCAMLBUILD :=\
  ocamlbuild \
    -classic-display \
    -cflag -unsafe-string \
    -j 4 \
    -use-ocamlfind \
    -use-menhir \
    -menhir "menhir -lg 1 -la 1 --explain" \
    -Is $(DIRS) \

.PHONY: all test clean

all:
	@ $(OCAMLBUILD) -quiet $(TARGET)
	@ ln -sf $(TARGET) $(JUNAC)

test: all
	@ make -C test test

clean:
	rm -f *~
	rm -f tests/*.c tests/*.out
	$(OCAMLBUILD) -clean
	rm -f $(TARGET) $(JUNAC)
	$(MAKE) -C test clean
