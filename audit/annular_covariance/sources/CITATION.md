# Fixed primary source: external reproducibility input

Yitang Zhang, *Discrete mean estimates and the Landau–Siegel zero*, arXiv:2211.02515v1, submitted 4 November 2022.

- [Version-specific abstract](https://arxiv.org/abs/2211.02515v1)
- [Official version-specific source download](https://arxiv.org/src/2211.02515v1)
- SHA256 of the extracted TeX file used in the original audits: `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`
- The version page identifies the paper's license as [Creative Commons Attribution 4.0](https://creativecommons.org/licenses/by/4.0/). This bundle does not redistribute the paper's full TeX or PDF. No author endorsement is implied.

## Optional source identity check

The complete paper is an external input, not a bundled file. Obtain the v1 source from the official link, unpack its archive locally, and identify the TeX file whose bytes have the SHA256 above. The hash applies to the extracted TeX, not to the downloaded archive. No network download is performed by the check scripts.

Supply that local file explicitly to run the optional identity check:

    python -B scripts/check_independent.py --source path/to/source.tex
    python -B scripts/run_checks.py --source path/to/source.tex

The paths above are relative to the caller's working directory; absolute user-supplied paths are also accepted. Without --source, all finite algebra checks run and the source-file hash check is explicitly reported as skipped. The finite checks do not parse or mathematically validate the paper.

The separately recorded source-input run verified the originally audited local TeX file at the stated hash; that file remains outside this public bundle. Obtaining an exact matching official source file is necessary only to reproduce that additional identity check, not to run the finite algebra suites.

This audit uses the source's definitions and hypotheses; it does not establish its final contradiction.
