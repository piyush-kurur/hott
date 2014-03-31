.PHONY: agda clean

all: agda

agda:
	make -C agda build

clean:
	make -C agda clean
