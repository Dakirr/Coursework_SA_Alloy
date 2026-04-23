module SA_init
enum Number {N0, N1, N2, N3, N4, N5}
enum ConstantQualityType {cigarettes, drink, nationality}
enum ChangingQualityType {House, pet}
let final_time = 101
let final_time_m_1 = sub[final_time, 1]

fun distance_arr: Number -> Number -> one Int {
	N0 -> N0 -> 0 +
	N0 -> N1 -> 101 +
	N0 -> N2 -> 101 +
	N0 -> N3 -> 2 +
	N0 -> N4 -> 3 +
	N0 -> N5 -> 2 +
	N1 -> N0 -> 101 +
	N1 -> N1 -> 0 +
	N1 -> N2 -> 2 +
	N1 -> N3 -> 3 +
	N1 -> N4 -> 1 +
	N1 -> N5 -> 101 +
	N2 -> N0 -> 101 +
	N2 -> N1 -> 2 +
	N2 -> N2 -> 0 +
	N2 -> N3 -> 2 +
	N2 -> N4 -> 3 +
	N2 -> N5 -> 101 +
	N3 -> N0 -> 2 +
	N3 -> N1 -> 3 +
	N3 -> N2 -> 2 +
	N3 -> N3 -> 0 +
	N3 -> N4 -> 3 +
	N3 -> N5 -> 2 +
	N4 -> N0 -> 3 +
	N4 -> N1 -> 1 +
	N4 -> N2 -> 3 +
	N4 -> N3 -> 3 +
	N4 -> N4 -> 0 +
	N4 -> N5 -> 101 +
	N5 -> N0 -> 2 +
	N5 -> N1 -> 101 +
	N5 -> N2 -> 101 +
	N5 -> N3 -> 2 +
	N5 -> N4 -> 101 +
	N5 -> N5 -> 0
}
fun distance [n1: Number, n2: Number] : one Int {
	distance_arr[n1][n2]
}

