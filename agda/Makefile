TEST_PROGS= compileCoreLibrary
AGDAC=agda -i . -c

.PHONY: build



build: ${TEST_PROGS}

${TEST_PROGS}:
	${AGDAC} tests/$@.agda

clean:
	rm -f ${TEST_PROGS}
	rm -rf MAlonzo
