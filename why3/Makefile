.SUFFIXES: .mlw .wh3

SRC = $(shell find . -name "*.mlw")
OUT = $(SRC:.mlw=.wh3)

all: $(OUT)
	echo $(OUT)

.mlw.wh3:
	why3 prove $< > $@

clean:
	rm $(OUT)

.PHONY: all
