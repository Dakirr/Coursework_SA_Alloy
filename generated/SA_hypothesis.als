module SA_hypothesis
open SA_init
open SA_lib
open SA_api

fact {
	HasQuality[N1, House, N1, T[2]]
	HasQuality[N1, House, N2, T[2]]
	HaveMetInHouse[N0, N1, T[2], N1]
	IsTravellingFromTo[N0, T[1], N0, N1]
	MustReturnHomeAfterTravel
}

run {} for 36 Quality, 3 Person, 12 MeetingEvent, 12 TravellingEvent, 36 ExchangeEvent, 4 Time