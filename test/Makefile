CC=@clang

EXAMPLE_C_FILES = $(shell find . -type f -name '*.c' | grep -v "runtime.c")
EXAMPLE_ELF_FILES = $(patsubst %.c, %.elf, $(EXAMPLE_C_FILES))

all: $(EXAMPLE_ELF_FILES)
%.elf: %.c
	$(CC) -fno-discard-value-names -O0 -Xclang -disable-O0-optnone -Wc2x-extensions -o $*.elf $<
	chmod +x $*.elf

clean:
	$(RM) -f *.elf
