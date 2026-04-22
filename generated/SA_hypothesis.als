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
	HasQuality[N1, House, N1, T[2]]
	HasQuality[N1, House, N2, T[2]]
}

run {} for 120 Quality, 6 Person, 24 MeetingEvent, 24 TravellingEvent, 120 ExchangeEvent, 4 Time