const express = require('express');
const TestObj = require('@example/test');

function basicTaint() {
    const app = express();
    app.use((req, res, next) => {
        req.tainted = source();
        req.safe = 'safe';
        next();
    });
    app.get('/', (req, res) => {
        sink(req.tainted); // NOT OK
        sink(req.safe); // OK
    });
}

function basicApiGraph() {
    const app = express();
    app.use((req, res, next) => {
        req.obj = new TestObj();
        next();
    });
    app.get('/', (req, res) => {
        sink(req.obj.getSource()); // NOT OK
        req.obj.getSink(source()); // NOT OK
    });
}

function noTaint() {
    const app = express();
    function middleware(req, res, next) {
        req.tainted = source();
        req.safe = 'safe';
        next();
    }
    app.get('/unsafe', middleware, (req, res) => {
        sink(req.tainted); // NOT OK
        sink(req.safe); // OK
    });
    app.get('/safe', (req, res) => {
        sink(req.tainted); // OK - not preceded by middleware
        sink(req.safe); // OK
    });
}

function looseApiGraphStep() {
    const app = express();
    function middleware(req, res, next) {
        req.obj = new TestObj();
        next();
    }
    app.get('/unsafe', middleware, (req, res) => {
        sink(req.obj.getSource()); // NOT OK
    });
    app.get('/safe', (req, res) => {
        sink(req.obj.getSource()); // NOT OK - we allow API graph steps within the same app
    });
}

function chainMiddlewares() {
    const app = express();
    function step1(req, res, next) {
        req.taint = source();
        next();
    }
    function step2(req, res, next) {
        req.locals.alsoTaint = req.taint;
        next();
    }
    app.get('/', step1, step2, (req, res) => {
        sink(req.taint); // NOT OK
        sink(req.locals.alsoTaint); // NOT OK
    });
}

function routerEscapesIntoParameter() {
    const app = express();
    function setupMiddlewares(router) {
        router.use((req, res, next) => {
            req.taint = source();
            next();
        });
    }
    app.get('/before', (req, res) => {
        sink(req.taint); // OK
    });
    setupMiddlewares(app);
    app.get('/after', (req, res) => {
        sink(req.taint); // NOT OK
    });
}

function routerReturned() {
    const app = express();
    function makeMiddlewares() {
        let router = new express.Router();
        router.use((req, res, next) => {
            req.taint = source();
            next();
        });
        return router;
    }
    app.get('/before', (req, res) => {
        sink(req.taint); // OK
    });
    app.use(makeMiddlewares());
    app.get('/after', (req, res) => {
        sink(req.taint); // NOT OK
    });
}

function routerCaptured() {
    const app = express();
    function addMiddlewares() {
        app.use((req, res, next) => {
            req.taint = source();
            next();
        });
    }
    app.get('/before', (req, res) => {
        sink(req.taint); // OK
    });
    addMiddlewares();
    app.get('/after', (req, res) => {
        sink(req.taint); // NOT OK [INCONSISTENCY] - missing handling of side effects via captured variable
    });
}
