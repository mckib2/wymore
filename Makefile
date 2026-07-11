.PHONY: build check check-no-sorry

build:
	lake build Mbse

check: build check-no-sorry

check-no-sorry:
	./scripts/check_no_sorry.sh

report:
	lake exe mbse
