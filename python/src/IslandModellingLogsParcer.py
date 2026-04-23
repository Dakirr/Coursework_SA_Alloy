import yaml
import ast
from AlloyBuilder import AlloyBuilder

class LogsParcer:
    def __init__(self, path: str = "./res/island_modeling_logs/"):
        self.base_path = path
         
        with open(f"{self.base_path}setting.yaml", "r") as f:
            data = yaml.safe_load(f)
        
        self.players_num = data["num_people"]
        self.final_time = data["num_days"] + 1
        self.constant_quality_types = {"nationality", "drink", "cigarettes"}
        self.changing_quality_types = {"House", "pet"}
        self._quality_mappings = {
            "nationality": dict(), 
            "drink": dict(), 
            "cigarettes": dict(),
            "House": dict(),
            "pet": dict()
        }

        for agent_dict in data['agents']:
            id = agent_dict['id'] - 1
            for key in agent_dict.keys():
                value = agent_dict[key]
                if key in self._quality_mappings.keys():
                    self._quality_mappings[key].update({value: id})
                elif key == 'house_color':
                    self._quality_mappings["House"].update({value: id})
        
        self.distances = [
            [round(float(j)) for j in i.replace("]", " ").replace("nan", f"{self.final_time}").split(", ")]
                for i in data['distance_matrix'].replace("[", "").replace("]","").split("\n")]

        self.must_return_home_after_travel = data["mandatory_return"]
        self.alloy_builder = self._create_alloy_builder()

    def _create_alloy_builder(self) -> AlloyBuilder:
        ab = AlloyBuilder(
            self.players_num, 
            self.constant_quality_types, 
            self.changing_quality_types, 
            self.final_time, 
            self.distances
        )
        ab.set_must_return_home_after_travel(self.must_return_home_after_travel)
        return ab

    def get_alloy_builder(self) -> AlloyBuilder:
        return self.alloy_builder
    
    def _parse_action_log(self, line: str) -> dict[str, object]:
        line = line.strip("ActionFact(timestamp=")
        timestamp, line = line.split(", ", 1)
        timestamp = int(timestamp)
        line = line.strip("type=<ActionType.")
        event_type, line = line.split(": ", 1)
        line = line.split(">, actors=", 1)[1]
        actors, line = line.split(", metadata=", 1)
        actors = [int(i)-1 for i in actors.strip("(").strip(")").split(", ")]
        metadata = ast.literal_eval(line[:-2].replace("<", "\"").replace(">", "\""))
        
        return {"timestamp": timestamp, "event_type": event_type, "actors": actors, "data": metadata}

    def _parse_exchange_params(self, line: str) -> dict[str, object]:
        timestamp, line = line.split(", ", 1)
        timestamp = int(timestamp)
        line = line.strip("type=<Action.Type.")
        event_type, line = line.split(": ", 1)
        line = line.split(">, actors=", 1)[1]
        actors, line = line.split(", metadata=", 1)
        actors = [int(i)-1 for i in actors.strip("(").strip(")").split(", ")]
        metadata = dict()
        line = line.strip("{'from': ")
        from_val, line = line.split(", ", 1)
        from_val = int(from_val)
        line = line.strip("'to': ")
        to_val, line = line.split(", ", 1)
        to_val = int(to_val)
        line = line.strip("'item: '")
        if (event_type == "PET_SWAP"):
            pet = line.split(" ", 1)[1].split("]")[0].strip(")")[1:-3]
            return {"timestamp": timestamp, "event_type": "QUALITY_EXCHANGE", "actors": actors, "data": {"quality": "pet", "value": pet}}
        elif (event_type == "HOUSE_SWAP"):
            house_id, line = line.strip("House(id=").split(", ", 1)
            return {"timestamp": timestamp, "event_type": "HOUSE_EXCHANGE", "actors": actors, "data": {"value": int(house_id)}}
        else:
            raise AssertionError("event_type should be in {PET_SWAP, HOUSE_SWAP}")

    def _parse_exchange_log(self, line: str) -> None:
        log = line.strip("[").strip("]")
        actions = log.split(", Action")
        actions = [self._parse_exchange_params(action.strip("Action").strip("Fact").strip("(timestamp=").strip(")")) for action in actions]
        for action in actions:
            if action['event_type'] == 'QUALITY_EXCHANGE':
                self.alloy_builder.add_have_exchanged_clause(
                    action['actors'][0],
                    action['actors'][1],
                    action['timestamp'],
                    action['data']['quality'] 
                )
                self.alloy_builder.add_has_quality_clause(
                    action['actors'][0],
                    action['data']['quality'],
                    self._quality_mappings['pet'][action['data']['value']],
                    action['timestamp']
                )
            elif action['event_type'] == 'HOUSE_EXCHANGE':
                self.alloy_builder.add_have_exchanged_clause(
                    action['actors'][0],
                    action['actors'][1],
                    action['timestamp'],
                    "House" 
                )
                self.alloy_builder.add_has_quality_clause(
                    action['actors'][0],
                    "House",
                    action['data']['value'] - 1,
                    action['timestamp']
                )
            else:
                raise AssertionError("event_type should be in {PET_SWAP, HOUSE_SWAP}")
            
    def add_facts_from_file_as_clauses(self, path: str, is_relative: bool = True) -> None:
        full_path : str
        if is_relative:
            full_path = f"{self.base_path}/{path}"
        else:
            full_path = path
        
        with open(full_path, "r") as f:
            for line in f:
                if line[0] == "[":
                    self._parse_exchange_log(line)
                else: 
                    log = self._parse_action_log(line)
                    if log['timestamp'] >= self.final_time:
                        break
                    if log["event_type"] == "START_TRIP":
                        clause =  f"one te : TravellingEvent | " 
                        clause += f"te.start = T[{log['data']['start']}] "
                        clause += f"and te.arrival = T[{log['data']['end']}] "
                        clause += f"and te.from = N{log['data']['from'] - 1} "
                        clause += f"and te.to = N{log['data']['to'] - 1} "
                        clause += f"and te.person = P[N{log['actors'][0]}]"
                        self.alloy_builder.add_clause(clause)
                    elif log["event_type"] == "MEETING":
                        self.alloy_builder.add_have_met_group_clause(log['actors'], log['timestamp'], log["data"]["house_at"] - 1)     
                    