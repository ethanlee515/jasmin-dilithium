#include <iostream>
#include <random>
#include <cstring>

extern "C" {
#include "../dilithium/ref/api.h"
#include "../dilithium/ref/params.h"
}

using std::cout;
using std::endl;
using std::vector;
using std::memcmp;

#define PRINT(X) cout << (#X) << " = " << (X) << endl

extern "C" {
	uint8_t verify_jazz(uint8_t signature[pqcrystals_dilithium3_BYTES],
			uint8_t* msg,
			uint64_t m_len,
			uint8_t pk[pqcrystals_dilithium3_PUBLICKEYBYTES]);
}

uint8_t sampleByte() {
	static std::random_device rd;
	static std::mt19937 gen(rd());
	static std::uniform_int_distribution<> distrib(0,  255);
	return distrib(gen);
}

void test_verify() {
	uint8_t pk[pqcrystals_dilithium3_PUBLICKEYBYTES];
	uint8_t sk[pqcrystals_dilithium3_SECRETKEYBYTES];
	pqcrystals_dilithium3_ref_keypair(pk, sk);

	uint8_t pk2[pqcrystals_dilithium3_PUBLICKEYBYTES];
	uint8_t sk2[pqcrystals_dilithium3_SECRETKEYBYTES];
	pqcrystals_dilithium3_ref_keypair(pk2, sk2);

	uint8_t m[1000];
	uint8_t m2[1000];
	for(int i = 0; i < 1000; ++i) {
		m[i] = sampleByte();
		m2[i] = sampleByte();
	}

	uint8_t sig[pqcrystals_dilithium3_BYTES];
	uint8_t sig2[pqcrystals_dilithium3_BYTES];

	size_t siglen;
	pqcrystals_dilithium3_ref_signature(sig, &siglen, m, 1000, sk);
	pqcrystals_dilithium3_ref_signature(sig2, &siglen, m, 1000, sk);

	if(!verify_jazz(sig, m, 1000, pk))
		throw runtime_error("test failed at " + to_string(__LINE__));

	if(verify_jazz(sig2, m2, 1000, pk))
		throw runtime_error("test failed at " + to_string(__LINE__));

	if(verify_jazz(sig2, m, 1000, pk))
		throw runtime_error("test failed at " + to_string(__LINE__));
}

int main() {
	for(int i = 0; i < 100; ++i)
		test_verify();
	return 0;
}
