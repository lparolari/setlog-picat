# BIN: output directory for compiled test files.
# SOURCES: sources files.
# TESTS: tests files.
# PICAT: picat interpreter.
# EXEC: test execution script.

BIN_DIR=bin
SRC_DIR=../src
PICAT=picat
EXEC=go_tests

all: tests

tests:
	mkdir -p $(BIN_DIR)
	find $(SRC_DIR) -name "*.qi" -type f -delete
	find $(BIN_DIR) -name "*.qi" -type f -delete
	cp $(SRC_DIR)/*.pi $(BIN_DIR)
	cp -f *_test.pi $(BIN_DIR)
	echo "$(PICAT) $(BIN_DIR)/solver_test.pi" > $(EXEC)
	echo "$(PICAT) $(BIN_DIR)/lset_test.pi" > go1
	chmod a+x $(EXEC) go1

clear:
	rm -f $(EXEC)
	rm -rf $(BIN_DIR)