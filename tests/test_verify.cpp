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

int main() {
	uint8_t pk[pqcrystals_dilithium3_PUBLICKEYBYTES];
	uint8_t sk[pqcrystals_dilithium3_SECRETKEYBYTES];

	uint8_t randomness[32] = { 0 };
	for(int i = 0; i < 32; ++i)
		randomness[i] = sampleByte();

	pqcrystals_dilithium3_ref_seeded_keypair(pk, sk, randomness);

	uint8_t m[1000];
	for(int i = 0; i < 1000; ++i)
		m[i] = sampleByte();

	uint8_t signature[pqcrystals_dilithium3_BYTES];

	pqcrystals_dilithium3_ref_signature(signature, &siglen, m, 1000, sk);

	PRINT(int(verify_jazz(signature, m, 1000, pk)));


	//PRINT(memcmp(signature_ref, signature_jazz, pqcrystals_dilithium3_BYTES));

	return 0;
}
