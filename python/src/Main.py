from AlloyBuilder import AlloyBuilder
from IslandModellingLogsParcer import LogsParcer

def main():
    players_num = 3
    constant_quality_types = {"CoT1"}
    changing_quality_types = {"House", "ChT1"}
    final_time = 4
    distances = [[]]

    init_data = (players_num, constant_quality_types, changing_quality_types, final_time, distances)

    builder_hand = AlloyBuilder(*init_data) # Builder can be set up manually 

    logs_parcer = LogsParcer() # Getting parcer for simulation logs 
    logs_parcer.add_facts_from_file_as_clauses("facts/island_facts.txt") # Parcing logs from simulation to set up buider
    builder = logs_parcer.get_alloy_builder() # Getting ready builder

    builder.add_has_quality_clause(1, "House", 2, 3) # Player=1 had Quality with type=House, value=2 at time=3
    builder.add_has_quality_clause(1, "House", 3, 3)
    builder.add_have_exchanged_clause(1, 2, 3, "House") # Player=1 have met Player=2 at time=3 with quality=House
    builder.add_have_met_cause(1, 2, 3, 4) # Player=1 have met Player=2 at time=3 in house=4
    builder.add_have_met_group_clause({1, 2, 3}, 1, 2) # Players={1,2,3} have met at time=1 in House=2 
    builder.add_is_travelling_cause(1, 2, 3, 4) # Player=1 is travelling at time=2 from house=3 to house=4

    builder.build() # Create files for alloy solver

if __name__ == "__main__":
    main()