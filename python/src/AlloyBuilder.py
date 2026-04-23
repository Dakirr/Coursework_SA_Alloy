import os
import shutil

class AlloyBuilder:

    def __init__(
        self, 
        players_num: int, 
        constant_quality_types: set[str], 
        changing_quality_types: set[str], 
        final_time: int, 
        distances: list[list[int]] = None,
        path: str = "/generated"
    ): 
        assert players_num > 0, "players number should be at least 1"

        assert "House" in constant_quality_types or "House" in changing_quality_types, \
            "\"House\" quality type is mandatory"
        
        assert final_time > 0, "final time should be at least 1"

        self.players_num = players_num
        self.constant_quality_types = constant_quality_types
        self.changing_quality_types = changing_quality_types
        self.final_time = final_time
        self.distances = distances
        self.clauses = ""
        self.dir = path
        self.must_return_home_after_travel = True
    
    def set_must_return_home_after_travel(self, value: bool) -> None:
        self.must_return_home_after_travel = value

    def _assert_in_bounds(self, number: int, name: str = "") -> None:
        if (name == ""):
            assert number >= 0 and number <= self.players_num, \
                f"variables with type \'Number\' should be in boundaries [0, {self.players_num}], got {number}"
        else:
            assert number >= 0 and number <= self.players_num, \
                f"variable {name} should be in boundaries [0, {self.players_num}], got {number}"
        
    def _assert_correct_time(self, number: int) -> None:
        assert number >= 0 and number < self.final_time, \
            f"variables with type 'Number' should be in boundaries [0, {self.final_time}), got {number}"
        
    def _assert_quality_type_exists(self, quality_type: str) -> None:
        assert quality_type in self.changing_quality_types or quality_type in self.constant_quality_types, \
            f"quality type should be in {self.changing_quality_types + self.constant_quality_types}, got {quality_type}"
    
    def _assert_quality_type_not_constant(self, quality_type: str) -> None:
        self._assert_quality_type_exists(quality_type)
        assert quality_type in self.changing_quality_types, \
            f"quality type should not be constant"

    def generate_distances(self) -> str:
        if self.distances is None:
            return "fun distance [n1: Number, n2: Number] : one Int {\n\t{1}\n}\n"
        else:
            assert len(self.distances) == self.players_num, \
                f"matrix of distances must be {self.players_num} by {self.players_num}"
            for row in self.distances:
                assert len(row) == self.players_num, \
                    f"matrix of distances must be {self.players_num} by {self.players_num}"
                
            res = "fun distance_arr: Number -> Number -> one Int {\n"
            for i in range(self.players_num):
                for j in range(self.players_num):
                    res += f"\tN{i} -> N{j} -> {self.distances[i][j]}"
                    if i != self.players_num - 1 or j != self.players_num - 1:
                        res += " +\n"
                    else:
                        res += "\n"
            res += "}\nfun distance [n1: Number, n2: Number] : one Int {\n\tdistance_arr[n1][n2]\n}\n\n"
            return res
        
    def generate_init_file(self) -> str:
        res = ""
        res =  "module SA_init\n"
        res += "enum Number {" + ", ".join(["N" + str(i) for i in range(self.players_num)]) + "}\n"
        res += "enum ConstantQualityType {" + ", ".join(self.constant_quality_types) + "}\n"
        res += "enum ChangingQualityType {" + ", ".join(self.changing_quality_types) + "}\n"
        res += f"let final_time = {self.final_time}\n"
        res += f"let final_time_m_1 = sub[final_time, 1]\n\n"

        res += self.generate_distances()
        return res 

    def add_clause(self, clause: str) -> None:
        self.clauses += f"\t{clause}\n"

    def add_has_quality_clause(
        self, 
        person_num: int, 
        quality_type: str, 
        quality_num: int, 
        time: int
    ) -> None:
        self._assert_in_bounds(person_num, "Person Number")
        self._assert_in_bounds(quality_num, "Quality Number")
        self._assert_correct_time(time)
        self._assert_quality_type_exists(quality_type)
        self.add_clause(f"HasQuality[N{person_num}, {quality_type}, N{quality_num}, T[{time}]]")

    def add_is_travelling_cause(
            self, 
            person_num: int, 
            time: int, 
            from_house: int = None, 
            to_house: int = None
    ) -> None:
        self._assert_in_bounds(person_num, "Person Number")
        self._assert_correct_time(time)

        if (from_house is not None and to_house is not None):
            self._assert_in_bounds(from_house, "From House")
            self._assert_in_bounds(to_house, "To House")
            self.add_clause(f"IsTravellingFromTo[N{person_num}, T[{time}], N{from_house}, N{to_house}]")
        elif (from_house is not None):
            self._assert_in_bounds(from_house, "From House")
            self.add_clause(f"IsTravellingFrom[N{person_num}, T[{time}], N{from_house}]")
        elif (to_house is not None):
            self._assert_in_bounds(to_house, "To House")
            self.add_clause(f"IsTravellingFrom[N{person_num}, T[{time}], N{to_house}]")
        else:
            self.add_clause(f"IsTravelling[N{person_num}, T[{time}]]")

    def add_have_met_cause(
        self, 
        person1_num: int, 
        person2_num: int, 
        time: int,
        house_num: int = None
    ) -> None:
        self._assert_in_bounds(person1_num, "Person 1 Number")
        self._assert_in_bounds(person2_num, "Person 2 Number")
        self._assert_correct_time(time)

        if house_num is not None:
            self._assert_in_bounds(house_num, "House Number")
            self.add_clause(f"HaveMetInHouse[N{person1_num}, N{person2_num}, T[{time}], N{house_num}]")
        else:
            self.add_clause(f"HaveMet[N{person1_num}, N{person2_num}, T[{time}]]")

    def add_have_met_group_clause(
        self,
        people: set[int],
        time: int,
        house_num: int = None
    ) -> None:
        for p in people:
            self._assert_in_bounds(p)
        self._assert_correct_time(time)
        if house_num is not None:
            self._assert_in_bounds(house_num, "House Number")
            self.add_clause(f"GroupHaveMetInHouse[{' + '.join(['N'+str(i) for i in people])}, T[{time}], N{house_num}]")
        else:
            self.add_clause(f"GroupHaveMet[{' + '.join(['N'+str(i) for i in people])}, T[{time}]]")

    
    def add_have_exchanged_clause(
        self,
        person1_num: int,
        person2_num: int,
        time: int, 
        quality_type: str
    ):
        self._assert_in_bounds(person1_num, "Person 1 Number")
        self._assert_in_bounds(person2_num, "Person 2 Number")
        self._assert_correct_time(time)
        self._assert_quality_type_not_constant(quality_type)
        self.add_clause(f"ExchangedWithQuality[N{person1_num}, N{person2_num}, {quality_type}, T[{time}]]") 

    def generate_hypothesis_file(self):
        res = ""
        res =  "module SA_hypothesis\n"
        res += "open SA_init\n"
        res += "open SA_lib\n"
        res += "open SA_api\n"

        if (self.must_return_home_after_travel):
            self.add_clause("MustReturnHomeAfterTravel")

        res += "\nfact {\n"
        res += self.clauses 
        res += "}\n\n"

        quality_count = len(self.constant_quality_types) + len(self.changing_quality_types)
        res += "run {} " + \
        f"for {self.final_time*self.players_num*quality_count} Quality, " + \
        f"{self.players_num} Person, " + \
        f"{self.final_time*self.players_num} MeetingEvent, " + \
        f"{self.final_time*self.players_num} TravellingEvent, " + \
        f"{self.final_time*self.players_num*quality_count} ExchangeEvent, " + \
        f"{self.final_time} Time"
        return res 

    def build(self):
        shutil.rmtree(self.dir, ignore_errors = True) 
        os.makedirs(self.dir, exist_ok=True)

        with open(f"{self.dir}/SA_init.als", "w") as file:
            file.write(self.generate_init_file())

        with open(f"{self.dir}/SA_hypothesis.als", "w") as file:
            file.write(self.generate_hypothesis_file())
