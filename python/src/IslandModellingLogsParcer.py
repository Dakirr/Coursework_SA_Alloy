import yaml
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
            [float(j) for j in i.replace("]", " ").replace("nan", f"{self.final_time}").split(", ")]
                for i in data['distance_matrix'].replace("[", "").replace("]","").split("\n")]

        self.must_return_home_after_travel = data["mandatory_return"]

    def get_alloy_builder(self) -> AlloyBuilder:
        ab = AlloyBuilder(
            self.players_num, 
            self.constant_quality_types, 
            self.changing_quality_types, 
            self.final_time, 
            self.distances
        )
        ab.set_must_return_home_after_travel(self.must_return_home_after_travel)
        return ab
   