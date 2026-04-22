from AlloyBuilder import *

def main():
    players_num = 3
    constant_quality_types = ["CoT1"]
    changing_quality_types = ["House", "ChT1"]
    final_time = 4
    distances = [[]]

    init_data = (players_num, constant_quality_types, changing_quality_types, final_time, distances)

    builder = AlloyBuilder(*init_data)
    builder.add_has_quality_clause(1, "House", 1, 2)
    builder.add_has_quality_clause(1, "House", 2, 2)
    builder.add_have_met_cause(0, 1, 2, 1)
    builder.add_is_travelling_cause(0, 1, 0, 1)
    builder.build()

if __name__ == "__main__":
    main()