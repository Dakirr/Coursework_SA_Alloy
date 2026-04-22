module SA_hypothesis
open SA_init
open SA_lib
open SA_api

fact {
	HasQuality[N1, House, N1, T[2]]
	HasQuality[N1, House, N2, T[2]]
	HaveMetInHouse[N0, N1, T[2], N1]
	IsTravellingFromTo[N0, T[1], N0, N1]
}

run {} for 9030 Quality, 6 Person, 1806 MeetingEvent, 1806 TravellingEvent, 9030 ExchangeEvent, 301 Time