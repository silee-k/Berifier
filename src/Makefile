BUILD_DIR=build
TARGET=${BUILD_DIR}/Berifier
TEST_DIR=../test
EXAMPLE_ELF_FILES = $(shell find ../ -type f -name '*.elf')
EXAMPLE_OUTPUT_FILES = $(patsubst %.elf, %.output, $(EXAMPLE_ELF_FILES))
EXAMPLE_CHECK_FILES = $(patsubst %.elf, %.check, $(EXAMPLE_ELF_FILES))

all: build

build:
	dotnet build -o ${BUILD_DIR}

build_test:
	cd ${TEST_DIR} && make

test: clean_test ${EXAMPLE_OUTPUT_FILES}

check: ${EXAMPLE_CHECK_FILES}

%.check: %.output
	-diff $*.expected $<

%.output: %.elf
	-timeout 10 ${TARGET} $<|head -n 1 > $*.output

clean_test:
	rm -f ${TEST_DIR}/*.output

clean_elf:
	rm -f ${TEST_DIR}/*.elf

clean: clean_elf clean_test
	rm -rf build bin obj
