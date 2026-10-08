import MatrixRegression

set_option pp.universes true
set_option pp.proofs false

#print PiWeightedColon.BlockIndex
#print axioms PiWeightedColon.BlockIndex

#print PiWeightedColon.BlockLabel
#print axioms PiWeightedColon.BlockLabel

#check PiWeightedColon.block_div
#print axioms PiWeightedColon.block_div

#print PiWeightedColon.blockEncode
#print axioms PiWeightedColon.blockEncode

#print PiWeightedColon.blockDecode
#print axioms PiWeightedColon.blockDecode

#check PiWeightedColon.blockEncode_injective
#print axioms PiWeightedColon.blockEncode_injective

#check PiWeightedColon.blockEncode_decode
#print axioms PiWeightedColon.blockEncode_decode

#print PiWeightedColon.blockEquiv
#print axioms PiWeightedColon.blockEquiv

#print PiWeightedColon.RowIndex
#print axioms PiWeightedColon.RowIndex

#print PiWeightedColon.ColIndex
#print axioms PiWeightedColon.ColIndex

#print PiWeightedColon.rowS
#print axioms PiWeightedColon.rowS

#print PiWeightedColon.rowA
#print axioms PiWeightedColon.rowA

#print PiWeightedColon.colE
#print axioms PiWeightedColon.colE

#print PiWeightedColon.colC
#print axioms PiWeightedColon.colC

#print PiWeightedColon.colK
#print axioms PiWeightedColon.colK

#check PiWeightedColon.endpointD_pos
#print axioms PiWeightedColon.endpointD_pos

#print PiWeightedColon.RowLabel
#print axioms PiWeightedColon.RowLabel

#print PiWeightedColon.ColLabel
#print axioms PiWeightedColon.ColLabel

#print PiWeightedColon.rowLabelEquiv
#print axioms PiWeightedColon.rowLabelEquiv

#print PiWeightedColon.colLabelEquiv
#print axioms PiWeightedColon.colLabelEquiv

#check PiWeightedColon.row_index_bounds
#print axioms PiWeightedColon.row_index_bounds

#check PiWeightedColon.col_index_bounds
#print axioms PiWeightedColon.col_index_bounds

#check PiWeightedColon.blockIndex_card
#print axioms PiWeightedColon.blockIndex_card

#check PiWeightedColon.common_index_count
#print axioms PiWeightedColon.common_index_count

#check PiWeightedColon.rowIndex_card
#print axioms PiWeightedColon.rowIndex_card

#check PiWeightedColon.colIndex_card
#print axioms PiWeightedColon.colIndex_card

#print PiWeightedColon.rowLabelFintype
#print axioms PiWeightedColon.rowLabelFintype

#print PiWeightedColon.colLabelFintype
#print axioms PiWeightedColon.colLabelFintype

#check PiWeightedColon.rowLabel_card
#print axioms PiWeightedColon.rowLabel_card

#check PiWeightedColon.colLabel_card
#print axioms PiWeightedColon.colLabel_card

#print PiWeightedColon.matrixIndexEquiv
#print axioms PiWeightedColon.matrixIndexEquiv

#print PiWeightedColon.binaryEntry
#print axioms PiWeightedColon.binaryEntry

#check PiWeightedColon.entry_exponent_integer
#print axioms PiWeightedColon.entry_exponent_integer

#check PiWeightedColon.coordinate_bimono_coeff
#print axioms PiWeightedColon.coordinate_bimono_coeff

#check PiWeightedColon.coordinate_mono_coeff
#print axioms PiWeightedColon.coordinate_mono_coeff

#print PiWeightedColon.binaryMatrix
#print axioms PiWeightedColon.binaryMatrix

#check PiWeightedColon.binaryMatrix_coefficient
#print axioms PiWeightedColon.binaryMatrix_coefficient

#check PiWeightedColon.low_weight_iff
#print axioms PiWeightedColon.low_weight_iff

#check PiWeightedColon.endpoint_data_iff
#print axioms PiWeightedColon.endpoint_data_iff

#check PiWeightedColon.dataIntersection_iff_columns
#print axioms PiWeightedColon.dataIntersection_iff_columns

#check PiWeightedColon.row_coordinates_injective
#print axioms PiWeightedColon.row_coordinates_injective

#check PiWeightedColon.coeff_bimono
#print axioms PiWeightedColon.coeff_bimono

#print PiWeightedColon.rowPolynomial
#print axioms PiWeightedColon.rowPolynomial

#check PiWeightedColon.rowPolynomial_mem
#print axioms PiWeightedColon.rowPolynomial_mem

#check PiWeightedColon.rowPolynomial_coeff
#print axioms PiWeightedColon.rowPolynomial_coeff

#check PiWeightedColon.rowPolynomial_columns
#print axioms PiWeightedColon.rowPolynomial_columns

#check PiWeightedColon.row_vector_dimension
#print axioms PiWeightedColon.row_vector_dimension

#check PiWeightedColon.col_vector_dimension
#print axioms PiWeightedColon.col_vector_dimension

#check PiWeightedColon.binaryMatrix_vecMul_eq_zero
#print axioms PiWeightedColon.binaryMatrix_vecMul_eq_zero

#print PiWeightedColon.squareBinaryMatrix
#print axioms PiWeightedColon.squareBinaryMatrix

#check PiWeightedColon.squareBinaryMatrix_vecMul_eq_zero
#print axioms PiWeightedColon.squareBinaryMatrix_vecMul_eq_zero

#check PiWeightedColon.squareBinaryMatrix_det_ne_zero
#print axioms PiWeightedColon.squareBinaryMatrix_det_ne_zero

#check PiWeightedColon.squareBinaryMatrix_isUnit
#print axioms PiWeightedColon.squareBinaryMatrix_isUnit

#check PiWeightedColon.squareBinaryMatrix_inverse
#print axioms PiWeightedColon.squareBinaryMatrix_inverse

#print PiWeightedColon.canonicalBinaryMatrix
#print axioms PiWeightedColon.canonicalBinaryMatrix

#check PiWeightedColon.canonicalBinaryMatrix_det_ne_zero
#print axioms PiWeightedColon.canonicalBinaryMatrix_det_ne_zero

#check PiWeightedColon.canonicalBinaryMatrix_isUnit
#print axioms PiWeightedColon.canonicalBinaryMatrix_isUnit

#check PiWeightedColon.Regression.small_matrix_index_counts
#print axioms PiWeightedColon.Regression.small_matrix_index_counts

#check PiWeightedColon.Regression.binary_entry_boundaries
#print axioms PiWeightedColon.Regression.binary_entry_boundaries

#check PiWeightedColon.Regression.binary_entry_guards_and_parity
#print axioms PiWeightedColon.Regression.binary_entry_guards_and_parity

#check PiWeightedColon.Regression.actual_coefficient_example
#print axioms PiWeightedColon.Regression.actual_coefficient_example

#print PiWeightedColon.Regression.testMatrixRow
#print axioms PiWeightedColon.Regression.testMatrixRow

#print PiWeightedColon.Regression.testMatrixCol
#print axioms PiWeightedColon.Regression.testMatrixCol

#check PiWeightedColon.Regression.actual_matrix_entry
#print axioms PiWeightedColon.Regression.actual_matrix_entry

#check PiWeightedColon.Regression.label_roundtrip_example
#print axioms PiWeightedColon.Regression.label_roundtrip_example
