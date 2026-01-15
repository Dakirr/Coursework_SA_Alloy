FROM alpine:3.18
RUN apk add --no-cache python3 py3-pip

WORKDIR /app

COPY script.py .

CMD ["python", "script.py"]