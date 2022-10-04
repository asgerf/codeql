export function Foo(props) {
    const data = {
        foo: {
            bar: props.data
        }
    }
    return <script type="application/ld+json" dangerouslySetInnerHTML={{ __html: JSON.stringify(data) }}></script> // NOT OK
}

ReactDOM.render(<Foo data={window.name}/>)
