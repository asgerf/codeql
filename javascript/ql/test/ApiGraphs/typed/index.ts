import * as mongodb from "mongodb";

const express = require("express") as any;
const bodyParser = require("body-parser") as any;

declare function getCollection(): mongodb.Collection;

let app = express();

app.use(bodyParser.json());

app.post("/find", (req, res) => {
  let v = JSON.parse(req.body.x);
  getCollection().find({ id: v }); // use=typeUse("mongodb","Collection").getMember("find")
});

import * as mongoose from "mongoose";
declare function getMongooseModel(): mongoose.Model;
declare function getMongooseQuery(): mongoose.Query;
app.post("/find", (req, res) => {
  let v = JSON.parse(req.body.x);
  getMongooseModel().find({ id: v }); // def=typeUse("mongoose","Model").getMember("find").getParameter(0)
  getMongooseQuery().find({ id: v }); // def=typeUse("mongoose","Query").getMember("find").getParameter(0)
});

import * as puppeteer from 'puppeteer';
class Renderer {
    private browser: puppeteer.Browser;
    foo(): void {
        const page = this.browser.newPage(); /* use=typeUse("puppeteer","Browser") */
    }
}