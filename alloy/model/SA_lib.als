module SA_lib
open SA_init

//
// Time
//

sig Time {
	t: one Int
}

fun clamp_time[i: Int]: Int {
    i < 0 => 0 else (i > final_time_m_1 => final_time_m_1 else i)
}

fact {
	all time: Int | (time >= 0 and time < final_time) implies (one T: Time | T.t = time)
}

fun T[i: Int]: one Time {
	{T: Time | T.t = clamp_time[i]}
} 

fun Prev [time: Time]: one Time {
	T[sub[time.t, 1]]
}

fun Next [time: Time]: one Time {
	T[add[time.t, 1]]
}

let StartTime = T[0]
let EndTime =  T[final_time_m_1]

//
// Person
//


sig Person {
	id: one Number
}

fact {
	all id1: Number | one p : Person | p.id = id1		
}

fun P[id1: Number] : one Person {
	{p1: Person | p1.id = id1}
}

//
// Quality
//

let QualityType = ConstantQualityType + ChangingQualityType

sig Quality {
	person: one Person,
	timestamp: one Time,
	type: one QualityType,
	value: one Number
}

fact {
	all qt1: QualityType | all t: Time | all value1: Number | one q1: Quality | q1.type = qt1 and q1.timestamp = t and q1.value = value1  // Существует ровно один объект Quality с сигнатурой (type0, value0, time0)
	all qt1: QualityType | all t: Time | all p1: Person | one q1: Quality | q1.type = qt1 and q1.timestamp = t and q1.person = p1  // Существует ровно один объект Quality с сигнатурой (type0, person0, time0)
	//some disj q1, q2: Quality | q1.type != q2.type or q1.value != q2.value or q1.timestamp != q2.timestamp 
	all q: Quality | q.timestamp = T[0] implies q.value = q.person.id // Инициализация
	all q: Quality | q.type in ConstantQualityType implies (all q1: Quality | (q1.type = q.type and q1.person = q.person implies q1.value = q.value)) // Константные качества константны
}

pred HasQualityTech[p: Person, q: Quality, t: Time] {
  	q.person = p and q.timestamp = t
}

pred HasQuality[num: Number, type1: QualityType, value1: Number, t: Time] {
  	some q: Quality | some p: Person | p.id = num and q.type = type1 and q.value = value1 and HasQualityTech[p, q, t]
}

//
// Events
//

pred IsInHouse [p: Person, h: Number, time: Time] {
	( // Если живем в доме и сейчас никуда не идем + ни в какой другой дом не пришли
		HasQuality[p.id, House, h, time] and no te: TravellingEvent | 
			te.person = p 
			and lte[te.start.t, time.t] 
			and (
				gt[te.arrival.t, time.t] 
				or (te.arrival = time and te.to != h)
			)
	) or ( // Если куда-то пришли и пока что не ушли
		one te: TravellingEvent | ( 
			te.person = p 
			and te.to = h
			and lte[te.arrival.t, time.t] 
			and no te1: TravellingEvent | (
				te1.person = p
				and te1.from = h
				and lte[te1.start.t, time.t]
				and gte[te1.start.t, te.arrival.t]
			)
		)
	)
}

sig TravellingEvent {
	start: one Time,
	arrival: one Time,
	person: one Person,
	from: one Number,
	to: one Number
}

pred IsTravellingTech [p: Person, t1: Time] {
	some te: TravellingEvent | te.person = p and lte[te.start.t, t1.t] and gte[te.arrival.t, t1.t]
}  

fact {
	all disj te1, te2: TravellingEvent | (te1.person = te2.person) implies (lt[te1.arrival.t, te2.start.t] or lt[te2.arrival.t, te1.start.t]) // Нет двух параллельных походов 
	all te: TravellingEvent | (te.from != te.to) // Не идем от себя к себе
	all te: TravellingEvent | (distance[te.from, te.to] = sub[te.arrival.t, te.start.t] or te.arrival.t = final_time_m_1) // Расстояние равно времени или путешествие не оканчивается
	all te: TravellingEvent | (IsInHouse[te.person, te.from, Prev[te.start]]) // Находимся в доме, из которого уходим
	all te: TravellingEvent | te.start != T[0] // В инициализационный момент ничего не происходит
	all p: Person | all h: Number | all t1: Time | // Не задерживаемся в чужом доме
	(	
		lt[t1.t, final_time_m_1]
		and (not HasQuality[p.id, House, h, Next[t1]])
		implies not (IsInHouse[p, h, t1] and IsInHouse[p, h, Next[t1]])
	)
}

sig MeetingEvent {
	timestamp: one Time,
	people: some Person,
	house: one Number
}

fact {
	all te: TravellingEvent | one me: MeetingEvent | me.timestamp = te.arrival and me.house = te.to // Travelling заканчивается Meeting
	all me: MeetingEvent | some te: TravellingEvent | me.timestamp = te.arrival and me.house = te.to // Meeting происходит после Travelling 
	all p: Person | all t: Time | lone me: MeetingEvent | me.timestamp = t and (p in me.people) // Каждый человек участвует не более, чем в одном Meeting Event в ход
	all h: Number | all t: Time | lone me: MeetingEvent | me.timestamp = t and (h = me.house)  // В каждом доме происходит не более, чем один Meeting Event в ход
	all me: MeetingEvent | all p: me.people | IsInHouse[p, me.house, me.timestamp] // Все люди в доме во время Meeting Event
	all p: Person | all h: Number | all t1: Time | all me: MeetingEvent | (me.house = h and me.timestamp = t1) and IsInHouse[p, h, t1] implies p in me.people // Все люди в доме с MeetingEvent в нем участвуют
}

sig ExchangeEvent {
	timestamp: one Time,
	p1: one Person,
	p2: one Person,
	type: one ChangingQualityType
}

fact {
	all ee: ExchangeEvent | ee.p1 != ee.p2 // Не меняемся сами с собой 
	all ee: ExchangeEvent | one me: MeetingEvent | ee.timestamp = me.timestamp and ee.p1 in me.people and ee.p2 in me.people // Exchange только при условии Meeting
	all p: Person | (some ExchangeEvent) implies (some ee: ExchangeEvent | ee.p1 = p implies (one ee_rev: ExchangeEvent | ee_rev.p2 = p and ee.timestamp = ee_rev.timestamp and ee.type = ee_rev.type)) // Если есть передача от человека, есть единственная передача ему
	all p: Person | all t: Time | all type1: ChangingQualityType | lone ee: ExchangeEvent | (ee.p1 = p and ee.timestamp = t and ee.type = type1) // Есть не более одной передачи от каждого человека
}

fact { // Если не произошел ExchangeEvent, качества сохраняются
        all q: Quality | 
	(
		q.type in ChangingQualityType 
		and q.timestamp.t < final_time - 1
		and no ee: ExchangeEvent | (
			ee.p2 = q.person 
			and q.type = ee.type 
			and ee.timestamp = q.timestamp
		)
	) implies (
		all q1: Quality |  ((q1.type = q.type and q1.person = q.person and q1.timestamp = Next[q.timestamp]) implies q1.value = q.value)
	)
}

fact { // Если произошел ExchangeEvent, качество меняется
  	all ee: ExchangeEvent | ee.timestamp.t < final_time - 1 implies {
      		let q1 = Quality & {q: Quality | q.person = ee.p1 and q.type = ee.type and q.timestamp = ee.timestamp} |
      		{
	      		some q2: Quality  {
	            	  	  q2.timestamp = Next[ee.timestamp]
			          q2.person = ee.p2
			          q2.type = ee.type
			          q2.value = q1.value
	        	}
      		}
    	}
}
