# Source attribution

The vendored OAI modules originate in [openai/math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a), commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. Its Apache License 2.0 text is retained in licenses/OpenAI-math-LICENSE.

The 12 PrimeNumberTheoremAnd/SiegelZeros support modules are the new-file additions from the same commit's [PrimeNumberTheoremAnd-lean4341.patch](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/patches/PrimeNumberTheoremAnd-lean4341.patch). The source manifest preserves their patch provenance and reconstructed Git blob hashes.

The Mertens support proofs copied into Splice/MertensSupport.lean retain attribution to [PrimeNumberTheoremAnd/IEANTN/Mertens.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/Mertens.lean), under Apache License 2.0. The extraction manifest records the unchanged proof chunks and the namespace/import adaptation.

Lean and Mathlib are fetched dependencies. Their license texts are retained in licenses/Lean-LICENSE and licenses/mathlib-LICENSE. Their exact versions and the remaining package revisions are recorded in project/lean-toolchain and project/lake-manifest.json. Dependency repositories retain their own notices and licenses.

The 69 raw source files have not been edited in this integration. Additional adapters and analytic/effective-search proofs are separated from the vendored raw namespaces and recorded by SOURCE_SHA256SUMS and verification/baseline.json.

