module SA_hypothesis
open SA_lib

pred IsTravelling [id: Number, t1: Time] {
	some te: TravellingEvent | te.person = P[id] and lte[te.start.t, t1.t] and gte[te.arrival.t, t1.t]
}  

pred IsTravellingFrom [id: Number, t1: Time, from1: Number] {
	some te: TravellingEvent | te.person = P[id] and lte[te.start.t, t1.t] and gte[te.arrival.t, t1.t] and te.from = from1
}

pred IsTravellingTo [id: Number, t1: Time, to1: Number] {
	some te: TravellingEvent | te.person = P[id] and lte[te.start.t, t1.t] and gte[te.arrival.t, t1.t] and te.to = to1 
}

pred IsTravellingFromTo [id: Number, t1: Time,  from1: Number, to1: Number] {
	some te: TravellingEvent | te.person = P[id] and lte[te.start.t, t1.t] and gte[te.arrival.t, t1.t] and te.from = from1 and te.to = to1 
}

pred HaveMet [p1: Number, p2: Number, t1: Time] {
	some me: MeetingEvent | P[p1] in me.people and P[p2] in me.people and me.timestamp = t1
}

pred HaveMetInHouse [p1: Number, p2: Number, t1: Time, h1: Number] {
	some me: MeetingEvent | P[p1] in me.people and P[p2] in me.people and me.timestamp = t1 and me.house = h1
}

pred GroupHaveMet [group: some Number, t1: Time] {
	some me: MeetingEvent | (all n: Number | n in group implies P[n] in me.people) and me.timestamp = t1
}

pred GroupHaveMetInHouse [group: some Number, t1: Time, h1: Number] {
	some me: MeetingEvent | (all n: Number | n in group implies P[n] in me.people) and me.timestamp = t1 and me.house = h1
}

pred ExchangedWithQuality [id1: Number, id2: Number, q: ChangingQualityType, t: Time] {
	some disj ee1, ee2: ExchangeEvent | 
		ee1.p1.id = id1 and ee1.p2.id = id2 and 
		ee2.p1.id = id2 and ee2.p2.id = id1 and 
		ee1.type = q and ee1.type = q and
		ee1.timestamp = t and ee2.timestamp = t 
}

pred MustReturnHomeAfterTravel { // Если флаг включен, идем домой после похода в гости
	all p: Person | all h: Number | all t1: Time |
	(	
		lt[t1.t, final_time]
		and (not HasQuality[p.id, House, h, Next[t1]]) 
		and IsInHouse[p, h, t1]
		implies 
		some h2: Number | some te: TravellingEvent |
		te.to = h2 and te.person = p and te.start = Next[t1] and HasQuality[p.id, House, h2, Next[t1]]
	)
}
