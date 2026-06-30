.PHONY: build check-no-sorry

build:
	lake build Mbse

check-no-sorry:
	./scripts/check_no_sorry.sh
