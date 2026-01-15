import os
import shutil

def main():
    output_dir = "/app/model"
    tmp_dir = "/output"

    players_num = 3
    constant_quality_types = ["CoT1"]
    changing_quality_type = ["House", "ChT1"]
    final_time = 6
    distances = [[]]


    shutil.rmtree(tmp_dir, ignore_errors = True) 
    os.makedirs(tmp_dir, exist_ok=True)

    res =  "module SA_init\n"
    res += "enum Number {" + ", ".join(["N" + str(i) for i in range(players_num)]) + "}\n"
    res += "enum ConstantQualityType {" + ", ".join(constant_quality_types) + "}\n"
    res += "enum ChangingQualityType {" + ", ".join(changing_quality_type) + "}\n"
    res += f"let final_time = {final_time}\n"

    # Пока захардкожены расстояния
    res += """
fun distance [n1: Number, n2: Number] : one Int {
    {1}
}
"""
    with open(f"{tmp_dir}/SA_init.als", "w") as file:
        file.write(res)


    res =  "module SA_hypothesis\n"
    res += "open SA_init\n"
    res += "open SA_lib\n"

    # Пока захардкожены условия
    res += """ 
fact {
    HasQuality[N0, House, N1, T[3]]
    HasQuality[N1, House, N2, T[3]]
}
"""
    res += "run {} " + f"for {final_time*players_num} Quality, {players_num} Person, {final_time*players_num} MeetingEvent, {final_time*players_num} TravellingEvent, {final_time*players_num} ExchangeEvent, {final_time} Time"
    with open(f"{tmp_dir}/SA_hypothesis.als", "w") as file:
        file.write(res)


if __name__ == "__main__":
    main()