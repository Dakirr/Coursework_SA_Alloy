module SA_hypothesis
open SA_init
open SA_lib

fact {
	HasQuality[N0, House, N1, T[3]]
	HasQuality[N1, House, N2, T[3]]
}
run {} for 100 Quality, 3 Person, 3 MeetingEvent, 5 TravellingEvent, 4 ExchangeEvent, 6 Time
