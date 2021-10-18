CXXFLAGS = -Wall -Wextra -Wpedantic -std=c++17 -DDILITHIUM_MODE=3
LDFLAGS = -I ../dilithium/ref -L../dilithium/ref -lpqcrystals_dilithium3_ref -lpqcrystals_fips202_ref

TESTS = test_keygen test_fft test_gen_matrix test_packing test_keygen_firsthalf test_hashing test_matrix_mult test_sign_fragments test_expandmask test_sign test_rounding

tests: $(TESTS)

test_keygen: test_keygen.cpp ../src/keygen.s ../dilithium/ref/randombytes.o
	$(CXX) $(CXXFLAGS) ../dilithium/ref/randombytes.o ../src/keygen.s test_keygen.cpp -o $@ $(LDFLAGS)

test_sign: test_sign.cpp ../src/sign.s ../dilithium/ref/randombytes.o
	$(CXX) $(CXXFLAGS) ../dilithium/ref/randombytes.o ../src/sign.s test_sign.cpp -o $@ $(LDFLAGS)

test_verify: test_verify.cpp ../src/verify.s ../dilithium/ref/randombytes.o
	$(CXX) $(CXXFLAGS) ../dilithium/ref/randombytes.o ../src/verify.s test_verify.cpp -o $@ $(LDFLAGS)

test_%: test_%.cpp %_export.s
	$(CXX) $(CXXFLAGS) ../dilithium/ref/randombytes.o $*_export.s test_$*.cpp -o $@ $(LDFLAGS)

%.s: %.jazz ../src/*.jazz
	jasminc -pasm $< > $@

clean:
	rm -f $(TESTS)
