FROM eclipse-temurin:21-jre-alpine

FROM eclipse-temurin:21-jre-alpine

WORKDIR /tmp  # NOT /app
COPY lib/ /app/lib/
COPY model/ /app/model/

CMD ["java", "-jar", "/app/lib/org.alloytools.alloy.dist.jar", "exec", "/app/model/SA_hypothesis.als", "-f"]