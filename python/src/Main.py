from AlloyBuilder import AlloyBuilder
from IslandModellingLogsParcer import LogsParcer

def main():
    players_num = 3
    constant_quality_types = {"CoT1"}
    changing_quality_types = {"House", "ChT1"}
    final_time = 4
    distances = [[]]

    init_data = (players_num, constant_quality_types, changing_quality_types, final_time, distances)

    logs_parcer = LogsParcer()
    logs_parcer.add_facts_from_file_as_clauses("facts/island_facts.txt")
    builder = logs_parcer.get_alloy_builder()
    builder.add_has_quality_clause(1, "House", 1, 2)
    builder.add_has_quality_clause(1, "House", 2, 2)
    builder.build()

if __name__ == "__main__":
    main()