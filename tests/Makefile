
BIN=bin                     # output directory for compiled test files.
SOURCES=../src/*         # sources files.
TESTS=*_test.pi             # tests files.
PICAT=picat                 # picat interpreter.
EXEC=go_tests               # test execution script.

all: tests

tests:
	mkdir -p $(BIN)
	cp -rf $(SOURCES) $(BIN)
	cp -f $(TESTS) $(BIN)
	echo "$(PICAT) $(BIN)/solver_test.pi" > $(EXEC)
	chmod a+x $(EXEC)

clear:
	rm -f $(EXEC)
	rm -rf $(BIN)