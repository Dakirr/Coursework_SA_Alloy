module SA_hypothesis
open SA_init
open SA_lib
open SA_api

fact {
	one te : TravellingEvent | te.start = T[1] and te.arrival = T[4] and te.from = N0 and te.to = N4 and te.person = P[N0]
	one te : TravellingEvent | te.start = T[1] and te.arrival = T[4] and te.from = N1 and te.to = N3 and te.person = P[N1]
	one te : TravellingEvent | te.start = T[1] and te.arrival = T[3] and te.from = N2 and te.to = N3 and te.person = P[N2]
	one te : TravellingEvent | te.start = T[1] and te.arrival = T[3] and te.from = N3 and te.to = N2 and te.person = P[N3]
	one te : TravellingEvent | te.start = T[1] and te.arrival = T[4] and te.from = N4 and te.to = N3 and te.person = P[N4]
	one te : TravellingEvent | te.start = T[1] and te.arrival = T[3] and te.from = N5 and te.to = N3 and te.person = P[N5]
	GroupHaveMetInHouse[N2 + N5, T[3], N3]
	one te : TravellingEvent | te.start = T[4] and te.arrival = T[7] and te.from = N3 and te.to = N1 and te.person = P[N2]
	one te : TravellingEvent | te.start = T[4] and te.arrival = T[6] and te.from = N2 and te.to = N3 and te.person = P[N3]
	one te : TravellingEvent | te.start = T[4] and te.arrival = T[6] and te.from = N3 and te.to = N0 and te.person = P[N5]
	GroupHaveMetInHouse[N1 + N4, T[4], N3]
	ExchangedWithQuality[N4, N1, pet, T[4]]
	HasQuality[N4, pet, N4, T[4]]
	ExchangedWithQuality[N1, N4, pet, T[4]]
	HasQuality[N1, pet, N1, T[4]]
	one te : TravellingEvent | te.start = T[5] and te.arrival = T[8] and te.from = N4 and te.to = N0 and te.person = P[N0]
	one te : TravellingEvent | te.start = T[5] and te.arrival = T[8] and te.from = N3 and te.to = N1 and te.person = P[N1]
	one te : TravellingEvent | te.start = T[5] and te.arrival = T[8] and te.from = N3 and te.to = N1 and te.person = P[N4]
	one te : TravellingEvent | te.start = T[7] and te.arrival = T[9] and te.from = N3 and te.to = N2 and te.person = P[N3]
	one te : TravellingEvent | te.start = T[7] and te.arrival = T[9] and te.from = N0 and te.to = N3 and te.person = P[N5]
	one te : TravellingEvent | te.start = T[8] and te.arrival = T[10] and te.from = N1 and te.to = N2 and te.person = P[N2]
	GroupHaveMetInHouse[N1 + N4, T[8], N1]
	ExchangedWithQuality[N4, N1, pet, T[8]]
	HasQuality[N4, pet, N1, T[8]]
	ExchangedWithQuality[N1, N4, pet, T[8]]
	HasQuality[N1, pet, N4, T[8]]
	one te : TravellingEvent | te.start = T[9] and te.arrival = T[11] and te.from = N0 and te.to = N3 and te.person = P[N0]
	one te : TravellingEvent | te.start = T[9] and te.arrival = T[12] and te.from = N1 and te.to = N3 and te.person = P[N1]
	one te : TravellingEvent | te.start = T[9] and te.arrival = T[12] and te.from = N1 and te.to = N3 and te.person = P[N4]
	one te : TravellingEvent | te.start = T[10] and te.arrival = T[13] and te.from = N2 and te.to = N4 and te.person = P[N3]
	one te : TravellingEvent | te.start = T[10] and te.arrival = T[13] and te.from = N3 and te.to = N4 and te.person = P[N5]
	HasQuality[N1, House, N2, T[3]]
	HasQuality[N1, House, N3, T[3]]
	ExchangedWithQuality[N1, N2, House, T[3]]
	HaveMetInHouse[N1, N2, T[3], N4]
	GroupHaveMetInHouse[N1 + N2 + N3, T[1], N2]
	IsTravellingFromTo[N1, T[2], N3, N4]
}

run {} for 330 Quality, 6 Person, 66 MeetingEvent, 66 TravellingEvent, 330 ExchangeEvent, 11 Time